import Lean
import StrataGenerators.Test.Types

/-!
# The property registry

The three attributes that let a property declare *itself* to the test harness. The author of a
property writes one declaration in one file:

```lean
@[strata_property]
def myPassIdempotent : TestDecl :=
  .property "mypass: the pass is idempotent" "mypass" Generators.program checkMyPass
```

`lake test` then runs it. You edit nothing inside this package. The attribute records the
*name* of the declaration in an environment extension, and `strata_registry%` in
`StrataGenerators.Test.Collect` expands to the list of each name in the current module and in
each module that it imports.

Lake uses this same mechanism for `@[test_driver]`. It is also the same idea as the inventory
that `ppx_quick_test` builds when a module starts, and as `#[quickcheck]` in Rust: the
registration is an effect of the declaration itself, and not a second edit in another place.

## What this can and cannot do for you

Lean links statically. Therefore a driver sees a declaration only if the module of the driver
imports the module of the declaration, directly or indirectly. This is the same need as
`mod tests;` in Rust, or as a file in a Dune library in OCaml. The generated import root
`StrataTests.lean` gives that last step.

If you add a property to a file that exists under `StrataTests/`, you need nothing more. If
you add or remove a *file*, run `lake exe write-test-imports`. That executable writes the root
again from the contents of the directory. See `StrataGenerators.Test.ImportRoot`. If you
forget, a driver rewrites the stale root and asks you to run it again, and `#verify_test_root`
fails the build. See `docs/writing-properties.md`.

## Order

The extension keeps the entries of one module in declaration order, and it keeps the modules
in import order. The order of a report is therefore the same on each run, and a reader can
review it in a diff. This is the reason for `registerPersistentEnvExtension` with a state of
type `Array`, in place of `registerTagAttribute` of the core library, whose `NameSet` state
loses the order.
-/

open Lean

namespace StrataGenerators.Test

/-- What a registration records: the declaration, and whether the declaration holds one
    `TestDecl` or a `List TestDecl`.

    `@[strata_property]` and `@[strata_properties]` write to the *same* extension. Therefore a
    file that uses both attributes still reports its properties in declaration order. Two
    extensions would put every list after every single property, and a reader would see that
    as a random order. -/
inductive Entry where
  /-- A `def _ : TestDecl`. -/
  | single (decl : Name)
  /-- A `def _ : List TestDecl`. The collector splices the list in place. -/
  | many (decl : Name)
  deriving Inhabited, Repr

/-- The registry. It holds the entries of one module in declaration order, and it holds the
    modules in import order. -/
initialize registryExt : PersistentEnvExtension Entry Entry (Array Entry) ←
  registerPersistentEnvExtension {
    name            := `StrataGenerators.Test.registryExt
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun s e => s.push e
    exportEntriesFn := fun es => es
  }

/-- Every entry. The imported entries come first, in import order. The entries of this module
    come after them, in declaration order. The function follows
    `Lake.OrderedTagAttribute.getAllEntries`. -/
def registryEntries (env : Environment) : Array Entry :=
  let s := registryExt.toEnvExtension.getState env
  s.importedEntries.flatMap id ++ s.state

/-! ## Attribute syntax

Both registration attributes take an optional weighting. A property can therefore state the
*distribution* it is checked over in the same place as its name and its check.

```lean
@[strata_property (tuning := stmtLoopHeavy)]
def loopElimZeroLoops : TestDecl :=
  .property "stmt: LoopElim eliminates all loops" fun (gs : GenStmts) => checkLoopElimZeroLoops gs.stmts

@[strata_property (tunings := [("default", stmtDefault), ("loop-heavy", stmtLoopHeavy)])]
def loopElimPreserves : TestDecl :=
  .property "stmt: LoopElim preserves typeability" fun gs => checkLoopElimPreservesTyping gs.stmts
```

`(tuning := θ)` registers the property with `θ`'s weights. `(tunings := [(label, θ), …])` registers
it once per weighting, and names each row `"⟨name⟩ [⟨label⟩]"`. The second form is usually the one you
want, because the useful question is whether a claim holds under a weighting *and* under the default.

The attribute needs a declaration of its own to hold the result. It therefore emits `⟨decl⟩.tuned` and
registers that instead. The emitted declaration is a `TestDecl`, or a `List TestDecl` for `tunings`.
The property the author wrote stays as it is and goes unregistered. Nothing user-visible changes,
because a report names a property by the string the property carries.

The mechanism is `TestDecl.withTuning`, and it needs no cooperation from the property's shape. The
retuning went into `Body.sampled` while `α` was still known, so the attribute is a one-line term. It
works for a `.property`, for a `.withPanel`, and for a whole `family`.

Two requests fail rather than go unnoticed: a property whose input type is not tunable, and a `θ`
whose length does not match its generator. Each becomes a property that reports the reason. A
`.withPanel` property keeps its verdict and loses its bespoke panel to the derived one, because a
hand-written panel closes over its own untuned sampler. `TestDecl.withTuning` says why.
-/

/-- The optional weighting on a registration attribute: `(tuning := θ)` for one, or
    `(tunings := [(label, θ), …])` for a labelled matrix. -/
syntax tuningSpec :=
  " (" (&"tuning" <|> &"tunings") " := " term ")"

syntax (name := strataPropertyAttr) "strata_property" (tuningSpec)? : attr
syntax (name := strataPropertiesAttr) "strata_properties" (tuningSpec)? : attr

/-- Which of the two forms was written, and the weighting term. -/
private inductive TuningArg where
  /-- `(tuning := θ)`: one weighting. -/
  | one (stx : Term)
  /-- `(tunings := [(label, θ), …])`: a labelled matrix. -/
  | many (stx : Term)

/-- Read the optional `tuningSpec` off an attribute's syntax. -/
private def parseTuningArg? (stx : Syntax) : Option TuningArg :=
  match stx with
  | `(attr| strata_property (tuning := $t)) | `(attr| strata_properties (tuning := $t)) =>
      some (.one t)
  | `(attr| strata_property (tunings := $t)) | `(attr| strata_properties (tunings := $t)) =>
      some (.many t)
  | _ => none

/-- The input type of a `TestDecl.property` application, when the value is recognisably one. It
    reads through a `withPanel`, through a `List.map`, and through the elements of a list literal,
    which is what `family` expands to. An empty result means "not a shape this can read", and not
    "not tunable".

    This function exists so that the common case fails at the declaration rather than at run time.
    `TestDecl.withTuning` is what applies a tuning, and it needs no help from here. The retuning went
    into `Body.sampled`, so a shape this function cannot read is still handled correctly. It reports
    the problem when the suite runs rather than when it compiles. -/
private partial def propertyInputTypes (e : Expr) : Array Expr :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf ``TestDecl.property then
    if h : 0 < args.size then #[args[0]] else #[]
  else if fn.isConstOf ``TestDecl.withPanel || fn.isConstOf ``TestDecl.withEnumeratedPanel then
    args.foldl (fun acc a => acc ++ propertyInputTypes a) #[]
  else if fn.isConstOf ``List.map || fn.isConstOf ``List.cons then
    args.foldl (fun acc a => acc ++ propertyInputTypes a) #[]
  else #[]

/-- Reject a tuning on an input type that has no `TunableGen` instance, when the property's shape
    shows the type. The message names the type, because "this type is not tunable" is the whole content
    of the mistake. -/
private def checkTunable (attrName : Name) (decl : Name) : AttrM Unit := do
  let some info := (← getEnv).find? decl | return
  let some value := info.value? | return
  Meta.MetaM.run' do
    for α in propertyInputTypes value do
      unless (← Meta.synthInstance? (← Meta.mkAppM ``TunableGen #[α])).isSome do
        throwError "`{attrName}`: the weights of `{α}`'s generator are not exposed, so a tuning \
          cannot be applied to a property over it.\n\
          Give `{α}` a `TunableGen` instance (see `StrataGenerators.Test.Generators`), or drop the \
          `tuning`/`tunings` argument."

/-- Emit `⟨decl⟩.tuned`, the tuned form of the tagged property, and return its name along with
    whether it holds one `TestDecl` or a list.

    `single` says whether the *tagged* declaration is one property or a family. That decides where the
    weighting goes: onto the property, or onto each member. -/
private def emitTuned (decl : Name) (arg : TuningArg) (single : Bool) :
    AttrM (Name × Bool) := do
  let tunedName := decl ++ `tuned
  let declIdent := mkIdent decl
  -- Build the value as syntax and let the elaborator do the work. The weighting is an arbitrary user
  -- term, such as a named profile or an inline `withWeights` call, so it must be elaborated in the
  -- module's context rather than reconstructed here.
  let spec : Term × Bool ← match arg, single with
    | .one t,  true  => do
        let v ← `(StrataGenerators.Test.TestDecl.withTuning $t "tuned" $declIdent)
        pure (v, false)
    | .one t,  false => do
        let v ← `(List.map (StrataGenerators.Test.TestDecl.withTuning $t "tuned") $declIdent)
        pure (v, true)
    | .many t, true  => do
        let v ← `(StrataGenerators.Test.TestDecl.underTuningsOf $t $declIdent)
        pure (v, true)
    | .many _, false => throwError
        "`strata_properties (tunings := …)`: a matrix of weightings over a family is ambiguous. Tag \
         each property with `@[strata_property (tunings := …)]`, or apply one weighting to the whole \
         family with `(tuning := θ)`"
  let (value, isList) := spec
  let type ← if isList then `(List StrataGenerators.Test.TestDecl)
             else `(StrataGenerators.Test.TestDecl)
  Meta.MetaM.run' <| Elab.Term.TermElabM.run' do
    let type ← Elab.Term.withSynthesize do
      let type ← Elab.Term.elabType type
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars type
    let value ← Elab.Term.withSynthesize do
      let value ← Elab.Term.elabTerm value type
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars value
    let value ← instantiateMVars value
    let type ← instantiateMVars type
    addAndCompile <| Declaration.defnDecl
      { name := tunedName, levelParams := [], type := type, value := value,
        hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  pure (tunedName, isList)

/-- Builds an attribute that records an entry in `registryExt`. `validate` checks that the
    declaration has the type that the collector gives to it later. A registration with the
    wrong type therefore fails at the declaration, and not as an unclear elaboration error
    inside `strata_registry%`.

    With a `tuningSpec` it registers the emitted `⟨decl⟩.tuned` instead. That may be a list even
    when the tagged declaration was a single property, because `tunings` turns one claim into one
    property per weighting.

    `name` and `userName` differ, and every message uses `userName`. These attributes take an
    argument, so they need a `syntax (name := …)` node, and `registerBuiltinAttribute`'s `name` must
    be that node's name for the parser to reach this handler. A message that reported `name` would
    name an attribute that nobody can write. -/
private def registerRegistryAttr (name userName : Name) (descr : String) (single : Bool)
    (validate : Name → AttrM Unit) (ref : Name := by exact decl_name%) : IO Unit :=
  registerBuiltinAttribute {
    ref, name, descr
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do throwAttrMustBeGlobal userName kind
      unless ((← getEnv).getModuleIdxFor? decl).isNone do
        throwAttrDeclInImportedModule userName decl
      validate decl
      let entry ← match parseTuningArg? stx with
        | none => pure (if single then Entry.single decl else Entry.many decl)
        | some arg =>
          checkTunable userName decl
          let (tunedName, isList) ← emitTuned decl arg single
          pure (if isList then Entry.many tunedName else Entry.single tunedName)
      modifyEnv fun env => registryExt.addEntry env entry
  }

/-- Checks that `decl` has the type that `expected` names. A registration that the collector
    cannot use therefore fails at the place of the mistake. The check compares only the head
    symbol, and that is what separates `TestDecl` from `List TestDecl`. -/
private def expectHead (attrName : Name) (expected : Name) (decl : Name) :
    AttrM Unit := do
  let some info := (← getEnv).find? decl
    | throwError "`{attrName}`: unknown declaration `{decl}`"
  let ty ← Meta.MetaM.run' (Meta.whnf info.type)
  unless ty.isAppOf expected do
    throwError "`{attrName}` expects a declaration whose type is headed by \
      `{expected}`, but `{decl}` has type{indentExpr info.type}"

/-- The attribute for one property. Attach it to a `def _ : TestDecl`. It also takes an optional
    `(tuning := θ)` or `(tunings := [(label, θ), …])`, which the syntax section above covers. -/
initialize
  registerRegistryAttr `strataPropertyAttr `strata_property
    "Register a `TestDecl` with the Strata property-test harness. Optionally \
     `(tuning := θ)` or `(tunings := [(label, θ), …])`."
    (single := true) (expectHead `strata_property ``TestDecl)

/-- The attribute for a family of properties. Attach it to a `def _ : List TestDecl`. Use it
    when one shared generator, or one list comprehension, gives many properties at one time. A
    property that stands alone uses `@[strata_property]`, so a search finds its name at its own
    declaration. `(tuning := θ)` applies one weighting to every member. -/
initialize
  registerRegistryAttr `strataPropertiesAttr `strata_properties
    "Register a `List TestDecl` with the Strata property-test harness. Optionally \
     `(tuning := θ)`, applied to every member."
    (single := false) (expectHead `strata_properties ``List)

/-- The registry of the diagnostics. It is separate from the property registry, because a
    driver runs the diagnostics at another point and they never gate the exit code. -/
initialize diagnosticExt : PersistentEnvExtension Name Name (Array Name) ←
  registerPersistentEnvExtension {
    name            := `StrataGenerators.Test.diagnosticExt
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun s n => s.push n
    exportEntriesFn := fun es => es
  }

/-- Every registered diagnostic. The imported entries come first, in import order. The entries
    of this module come after them, in declaration order. -/
def diagnosticEntries (env : Environment) : Array Name :=
  let s := diagnosticExt.toEnvExtension.getState env
  s.importedEntries.flatMap id ++ s.state

/-- The attribute for a diagnostic, which does not gate the exit code. Attach it to a
    `def _ : Diagnostic`. -/
initialize registerBuiltinAttribute {
  ref   := `StrataGenerators.Test.diagnosticAttr
  name  := `strata_diagnostic
  descr := "Register a `Diagnostic` with the Strata property-test harness."
  add   := fun decl stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == AttributeKind.global do
      throwAttrMustBeGlobal `strata_diagnostic kind
    unless ((← getEnv).getModuleIdxFor? decl).isNone do
      throwAttrDeclInImportedModule `strata_diagnostic decl
    expectHead `strata_diagnostic ``Diagnostic decl
    modifyEnv fun env => diagnosticExt.addEntry env decl
}

end StrataGenerators.Test
