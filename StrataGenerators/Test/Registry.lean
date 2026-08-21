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

/-- Builds an attribute that records `mk decl` in `registryExt`. `validate` checks that the
    declaration has the type that the collector gives to it later. A registration with the
    wrong type therefore fails at the declaration, and not as an unclear elaboration error
    inside `strata_registry%`. -/
private def registerRegistryAttr (name : Name) (descr : String) (mk : Name → Entry)
    (validate : Name → AttrM Unit) (ref : Name := by exact decl_name%) : IO Unit :=
  registerBuiltinAttribute {
    ref, name, descr
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal name kind
      unless ((← getEnv).getModuleIdxFor? decl).isNone do
        throwAttrDeclInImportedModule name decl
      validate decl
      modifyEnv fun env => registryExt.addEntry env (mk decl)
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

/-- The attribute for one property. Attach it to a `def _ : TestDecl`. -/
initialize
  registerRegistryAttr `strata_property
    "Register a `TestDecl` with the Strata property-test harness."
    Entry.single (expectHead `strata_property ``TestDecl)

/-- The attribute for a family of properties. Attach it to a `def _ : List TestDecl`. Use it
    when one shared generator, or one list comprehension, gives many properties at one time. A
    property that stands alone uses `@[strata_property]`, so a search finds its name at its own
    declaration. -/
initialize
  registerRegistryAttr `strata_properties
    "Register a `List TestDecl` with the Strata property-test harness."
    Entry.many (expectHead `strata_properties ``List)

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
