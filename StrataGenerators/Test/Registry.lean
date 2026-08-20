import Lean
import StrataGenerators.Test.Types

/-!
# The property registry

The three attributes that let a property declare *itself* to the test harness.
A property author writes one declaration in one file:

```lean
@[strata_property]
def myPassIdempotent : TestDecl :=
  .property "mypass: the pass is idempotent" "mypass" Generators.program checkMyPass
```

and `lake test` runs it. Nothing in this package's internals has to be edited:
the attribute records the declaration's *name* in an environment extension, and
`strata_registry%` (in `StrataGenerators.Test.Collect`) expands to the list of
every name recorded in the current module and in everything it imports.

This is the mechanism Lake itself uses for `@[test_driver]`
(`Lake/Util/OrderedTagAttribute.lean`), and the same idea as `ppx_quick_test`'s
module-initialisation inventory and Rust `quickcheck`'s `#[quickcheck]`:
registration is a side effect of writing the declaration, not a second edit
somewhere else.

## What this can and cannot automate

Lean links statically, so a declaration is visible to the driver only if the
driver's module transitively imports the module it lives in — the analogue of
`mod tests;` in Rust, or of a file being part of a Dune library in OCaml. That last
hop is the generated `StrataTests.lean` import root.

Adding a property to an existing file under `StrataTests/` needs nothing further.
Adding or removing a *file* needs `lake exe write-test-imports`, which rewrites the root
from the directory listing; see `StrataGenerators.Test.ImportRoot`. Forgetting is not
silent — the driver rewrites a stale root and asks to be re-run, and
`#verify_test_root` fails the build. See `docs/writing-properties.md`.

## Ordering

The extension keeps entries in declaration order within a module, and modules in
import order, so report order is stable across runs and reviewable in a diff.
That is why this uses `registerPersistentEnvExtension` with an `Array` state
rather than core's `registerTagAttribute`, whose `NameSet` state loses the order.
-/

open Lean

namespace StrataGenerators.Test

/-- What a registration records: the declaration, and whether it holds a single
    `TestDecl` or a `List TestDecl`.

    `@[strata_property]` and `@[strata_properties]` write to the *same* extension, so
    a file that mixes them still reports in the order it declares them. Two extensions
    would group every list after every single, which reads as a shuffle in the
    report. -/
inductive Entry where
  /-- A `def _ : TestDecl`. -/
  | single (decl : Name)
  /-- A `def _ : List TestDecl`, spliced in place. -/
  | many (decl : Name)
  deriving Inhabited, Repr

/-- The registry: entries in declaration order within a module, and modules in import
    order. -/
initialize registryExt : PersistentEnvExtension Entry Entry (Array Entry) ←
  registerPersistentEnvExtension {
    name            := `StrataGenerators.Test.registryExt
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun s e => s.push e
    exportEntriesFn := fun es => es
  }

/-- Every entry: imported ones first (in import order), then this module's (in
    declaration order). Modelled on `Lake.OrderedTagAttribute.getAllEntries`. -/
def registryEntries (env : Environment) : Array Entry :=
  let s := registryExt.toEnvExtension.getState env
  s.importedEntries.flatMap id ++ s.state

/-! ## Attribute syntax

Both registration attributes take an optional weighting, so a property can state the *distribution*
it is checked over where it states its name and its check:

```lean
@[strata_property (tuning := stmtLoopHeavy)]
def loopElimZeroLoops : TestDecl :=
  .property "stmt: LoopElim eliminates all loops" fun (gs : GenStmts) => checkLoopElimZeroLoops gs.stmts

@[strata_property (tunings := [("default", stmtDefault), ("loop-heavy", stmtLoopHeavy)])]
def loopElimPreserves : TestDecl :=
  .property "stmt: LoopElim preserves typeability" fun gs => checkLoopElimPreservesTyping gs.stmts
```

`(tuning := θ)` registers the property with `θ`'s weights. `(tunings := [(label, θ), …])` registers it
once per weighting, named `"⟨name⟩ [⟨label⟩]"` — usually what you want, since the useful question is
whether a claim holds under a weighting *and* under the default.

The attribute needs a declaration of its own to hold the result, so it emits `⟨decl⟩.tuned` (a
`TestDecl`, or a `List TestDecl` for `tunings`) and registers *that*. The property the author wrote
stays as it is, unregistered; nothing user-visible changes, because a property is reported under the
name in its own string.

The mechanism is `TestDecl.withTuning`, which needs no cooperation from the property's shape: the
retuning was recorded in `Body.sampled` when `α` was still known (see `MaybeTunable`), so the
attribute is a one-line term and works for a `.property`, a `.withPanel`, or a whole `family`. A
property whose input type is not tunable does not silently ignore the request — it becomes a property
that fails with the reason.
-/

/-- The optional weighting on a registration attribute: `(tuning := θ)` for one, or
    `(tunings := [(label, θ), …])` for a labelled matrix. -/
syntax tuningSpec :=
  " (" (&"tuning" <|> &"tunings") " := " term ")"

syntax (name := strataPropertyAttr) "strata_property" (tuningSpec)? : attr
syntax (name := strataPropertiesAttr) "strata_properties" (tuningSpec)? : attr

/-- Which of the two forms was written, and the weighting term. -/
private inductive TuningArg where
  /-- `(tuning := θ)` — one weighting. -/
  | one (stx : Term)
  /-- `(tunings := [(label, θ), …])` — a labelled matrix. -/
  | many (stx : Term)

/-- Read the optional `tuningSpec` off an attribute's syntax. -/
private def parseTuningArg? (stx : Syntax) : Option TuningArg :=
  match stx with
  | `(attr| strata_property (tuning := $t)) | `(attr| strata_properties (tuning := $t)) =>
      some (.one t)
  | `(attr| strata_property (tunings := $t)) | `(attr| strata_properties (tunings := $t)) =>
      some (.many t)
  | _ => none

/-- The input type of a `TestDecl.property` application, if the value is recognisably one — through
    a `withPanel`, a `List.map`, or the elements of a list literal, which is what `family` expands to.
    `none` means "not a shape this can read", not "not tunable".

    This exists only so that the common case fails at the declaration rather than at run time.
    `TestDecl.withTuning` is what actually applies a tuning, and it needs no help from here: the
    retuning was recorded in `Body.sampled`, so an unrecognised shape is still handled correctly — it
    just reports the problem when the suite runs instead of when it compiles. -/
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

/-- Reject a tuning on an input type with no `TunableGen` instance, where the property's shape lets us
    see the type. The message names the type, since "this type is not tunable" is the whole content of
    the mistake. -/
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

    `single` says whether the *tagged* declaration is one property or a family, which decides how the
    weighting is applied: to the property, or to each member. -/
private def emitTuned (decl : Name) (arg : TuningArg) (single : Bool) :
    AttrM (Name × Bool) := do
  let tunedName := decl ++ `tuned
  let declIdent := mkIdent decl
  -- Build the value as syntax and let the elaborator do the work: the weighting is an arbitrary
  -- user term (a named profile, or `stmtDefault.with […]` written inline), so it has to be
  -- elaborated in the module's context rather than reconstructed.
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
    | .many t, false => throwError
        "`strata_properties (tunings := …)`: a matrix of weightings over a family is ambiguous — \
         tag each property with `@[strata_property (tunings := …)]`, or apply one weighting to the \
         whole family with `(tuning := θ)`"
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

/-- An attribute that records `mk decl` in `registryExt`. `validate` is where it
    checks that the declaration has the type the collector will later ascribe to it,
    so a mistyped registration fails at the declaration rather than as a confusing
    elaboration failure inside `strata_registry%`.

    With a `tuningSpec` it registers the emitted `⟨decl⟩.tuned` instead, which may be a list even
    when the tagged declaration was a single property (`tunings` turns one claim into one property
    per weighting). -/
private def registerRegistryAttr (name : Name) (descr : String) (single : Bool)
    (validate : Name → AttrM Unit) (ref : Name := by exact decl_name%) : IO Unit :=
  registerBuiltinAttribute {
    ref, name, descr
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do throwAttrMustBeGlobal name kind
      unless ((← getEnv).getModuleIdxFor? decl).isNone do
        throwAttrDeclInImportedModule name decl
      validate decl
      let entry ← match parseTuningArg? stx with
        | none => pure (if single then Entry.single decl else Entry.many decl)
        | some arg =>
          checkTunable name decl
          let (tunedName, isList) ← emitTuned decl arg single
          pure (if isList then Entry.many tunedName else Entry.single tunedName)
      modifyEnv fun env => registryExt.addEntry env entry
  }

/-- Check that `decl` has the type `expected` names, so a registration the collector could not use is
    rejected where the mistake was made. `expected` is matched up to head symbol, which is what
    distinguishes `TestDecl` from `List TestDecl`. -/
private def expectHead (attrName : Name) (expected : Name) (decl : Name) :
    AttrM Unit := do
  let some info := (← getEnv).find? decl
    | throwError "`{attrName}`: unknown declaration `{decl}`"
  let ty ← Meta.MetaM.run' (Meta.whnf info.type)
  unless ty.isAppOf expected do
    throwError "`{attrName}` expects a declaration whose type is headed by \
      `{expected}`, but `{decl}` has type{indentExpr info.type}"

/-- One property, registering itself. Attach to a `def _ : TestDecl`. Optionally
    `(tuning := θ)` or `(tunings := [(label, θ), …])` — see the syntax section above. -/
initialize
  registerRegistryAttr `strataPropertyAttr
    "Register a `TestDecl` with the Strata property-test harness. Optionally \
     `(tuning := θ)` or `(tunings := [(label, θ), …])`."
    (single := true) (expectHead `strata_property ``TestDecl)

/-- A family of properties registered together. Attach to a `def _ : List TestDecl`.
    Use it when one shared generator or one list comprehension yields many properties
    at once; a standalone property should use `@[strata_property]`, so its name is
    greppable from its own declaration. `(tuning := θ)` applies one weighting to every
    member. -/
initialize
  registerRegistryAttr `strataPropertiesAttr
    "Register a `List TestDecl` with the Strata property-test harness. Optionally \
     `(tuning := θ)`, applied to every member."
    (single := false) (expectHead `strata_properties ``List)

/-- The diagnostics registry, kept separate because a driver runs it at a different
    point and it never gates the exit code. -/
initialize diagnosticExt : PersistentEnvExtension Name Name (Array Name) ←
  registerPersistentEnvExtension {
    name            := `StrataGenerators.Test.diagnosticExt
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun s n => s.push n
    exportEntriesFn := fun es => es
  }

def diagnosticEntries (env : Environment) : Array Name :=
  let s := diagnosticExt.toEnvExtension.getState env
  s.importedEntries.flatMap id ++ s.state

/-- A non-gating diagnostic. Attach to a `def _ : Diagnostic`. -/
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
