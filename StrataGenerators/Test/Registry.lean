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

and `lake test` runs it. An optional argument pins the property's seed, so it draws the
same inputs on every run:

```lean
@[strata_property (seed := 8021)]
def myRareDefect : TestDecl := …
```

Nothing in this package's internals has to be edited:
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
  | single (decl : Name) (seed : Option Nat)
  /-- A `def _ : List TestDecl`, spliced in place. `seed` pins every member. -/
  | many (decl : Name) (seed : Option Nat)
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

/-- The optional argument both registration attributes take: `(seed := 42)` pins the
    property's seed, so it draws the same inputs on every run. See
    `StrataGenerators.Test.withSeed`, which is what this expands to.

    One attribute with an argument, rather than a second attribute alongside it — the
    `@[strata_property, seed = 42]` that `ppx_quick_test`'s `[@config … seed = …]` would
    suggest. In Lean `@[a, b]` is a list of two *independent* attributes, so `seed = 42`
    would have to be a globally registered attribute called `seed`: a name any other
    package may also want, meaningless on its own, and — worst — a silent no-op on a
    declaration that forgot `strata_property`, since nothing would then be reading it.
    An argument cannot be written without the attribute it belongs to. This is the form
    core uses for the same reason: `@[deprecated (since := "2024-01-01")]`. -/
syntax seedArg := " (" &"seed" " := " num ")"

@[inherit_doc seedArg]
syntax (name := strata_property) "strata_property" (seedArg)? : attr

@[inherit_doc seedArg]
syntax (name := strata_properties) "strata_properties" (seedArg)? : attr

/-- Read the `(seed := N)` argument off an attribute, if it carries one. An argument that
    parsed but holds no numeral is an error rather than a silently absent pin: a pin that
    quietly failed to take would leave the property drawing fresh inputs while its author
    believed it was fixed to one draw. -/
private def seedOf? (stx : Syntax) : AttrM (Option Nat) := do
  let some arg := stx[1].getOptional? | return none
  let some n := (arg.find? (·.isOfKind numLitKind)).bind Syntax.isNatLit?
    | throwErrorAt arg "expected `(seed := N)` for a numeral `N`"
  return some n

/-- An attribute that records `mk decl seed?` in `registryExt`. `validate` is where it
    checks that the declaration has the type the collector will later ascribe to it,
    so a mistyped registration fails at the declaration rather than as a confusing
    elaboration failure inside `strata_registry%`. -/
private def registerRegistryAttr (name : Name) (descr : String)
    (mk : Name → Option Nat → Entry)
    (validate : Name → AttrM Unit) (ref : Name := by exact decl_name%) : IO Unit :=
  registerBuiltinAttribute {
    ref, name, descr
    add := fun decl stx kind => do
      unless kind == AttributeKind.global do throwAttrMustBeGlobal name kind
      unless ((← getEnv).getModuleIdxFor? decl).isNone do
        throwAttrDeclInImportedModule name decl
      validate decl
      let seed? ← seedOf? stx
      modifyEnv fun env => registryExt.addEntry env (mk decl seed?)
  }

/-- Check that `decl` has the type `expected` names, so a registration the
    collector could not use is rejected where the mistake was made. `expected` is
    matched up to head symbol, which is what distinguishes `TestDecl` from
    `List TestDecl`. -/
private def expectHead (attrName : Name) (expected : Name) (decl : Name) :
    AttrM Unit := do
  let some info := (← getEnv).find? decl
    | throwError "`{attrName}`: unknown declaration `{decl}`"
  let ty ← Meta.MetaM.run' (Meta.whnf info.type)
  unless ty.isAppOf expected do
    throwError "`{attrName}` expects a declaration whose type is headed by \
      `{expected}`, but `{decl}` has type{indentExpr info.type}"

/-- One property, registering itself. Attach to a `def _ : TestDecl`.

    `@[strata_property (seed := 42)]` also pins the property's seed. -/
initialize
  registerRegistryAttr `strata_property
    "Register a `TestDecl` with the Strata property-test harness. \
     `(seed := N)` pins the seed it draws its inputs from."
    Entry.single (expectHead `strata_property ``TestDecl)

/-- A family of properties registered together. Attach to a `def _ : List TestDecl`.
    Use it when one shared generator or one list comprehension yields many properties
    at once; a standalone property should use `@[strata_property]`, so its name is
    greppable from its own declaration. -/
initialize
  registerRegistryAttr `strata_properties
    "Register a `List TestDecl` with the Strata property-test harness. \
     `(seed := N)` pins that seed on every member of the list."
    Entry.many (expectHead `strata_properties ``List)

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
