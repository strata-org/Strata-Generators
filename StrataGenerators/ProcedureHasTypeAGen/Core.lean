import StrataGenerators.StmtHasTypeAGen
import Strata.Languages.Core.Procedure

open Lambda LExpr RandomChoice Core Imperative ArbString Std
open StrataGenerators.Stmt StrataGenerators.Function

/-!
# Core generator definition for well-typed Strata Core `Procedure`s

This file defines `genProcedure`, a generator of well-typed Strata Core
procedures (`Procedure`) satisfying the `ProcHasTypeA` relation of
`Strata.Languages.Core.ProcedureTypeSpec`.

## Design: in-out parameters via three disjoint signature blocks

`ProcHasType'` has eight obligations (see `ProcHasType'`). The generator produces:

- `typeArgs` — a `Nodup` list of type-variable names (via `genTypeArgs`, exactly
  as `genFunction`), discharging `typeArgsNodup`; the input/output types are
  drawn over these type arguments (`genLMonoTy typeArgs`), so `noUndeclaredVars`
  holds.
- three mutually-disjoint signature blocks, each a `Nodup`-keyed signature via
  `genInputs typeArgs`, made disjoint by `disjointInputs` filtering:
  * `inout` (`M`)      — parameters appearing in *both* input and output roles;
  * `inputOnly` (`I`)  — input-only parameters (filtered disjoint from `M`);
  * `outputOnly` (`O`) — output-only parameters (filtered disjoint from `M ++ I`).
  The signatures are front-aligned: `inputs := M ++ I`, `outputs := M ++ O`. So
  `getInoutParams = M` (the shared block), discharging `inputsNodup`/`outputsNodup`
  (each is an append of two disjoint `Nodup`-keyed blocks).
- `preconditions` / `postconditions` — labeled `bool` expressions (via
  `genChecks`). **Both** condition obligations reduce, under the annotated
  `instHasTypeA` (whose `exprTyped C Γ e mty = HasTypeA [] e mty` ignores the
  context), to `HasTypeA [] c.expr bool` — exactly what `genLExpr … .bool`
  produces — so neither depends on the input/body context.
- `body`     — a `structured` list of up to `len` statements, seeded with
  `inputs ++ outputs ++ oldVars M` as the initial `VarCtx` (mirroring the
  declarative `procBodyContext`, whose body scope is `inputScope ++ outputScope ++
  oldScope`) and with `inputs.keys ++ (oldVars M).keys` as the immutable names.
  The body may therefore freely *read* the inputs and the `old` bindings but can
  only *assign* to the output-only names `O` (`set` targets are drawn from the
  mutable sub-context, which excludes the immutable inputs and `old` bindings).
  This discharges `bodyTyped` (via `procBodyContext_inout`, which identifies the
  body context with `procToTCtx (inputs ++ outputs ++ oldVars M)`) and `modRights`
  (via `genStmts_mutableVars`, whose write-target tracking is over the mutable
  keys, i.e. exactly the output-only keys `O ⊆ outputs.keys`).

The threaded soundness invariant is the `Functional` predicate (not `Nodup`):
the in-out block `M` appears in both `inputs` and `outputs` bound to the *same*
type, so the seed has duplicate keys — but they agree on their values, and the
`old` keys (`"old " ++ name`, containing a space) never collide with the
space-free generated parameter names (`genIdentName_no_space`).

The body and contract expressions are generated at an **empty operator context**
(`octx = []`) and empty fvar/label contexts, matching the empty-context
instantiation both test harnesses use and for which expression-level soundness
is unconditional.
-/

namespace StrataGenerators.Procedure

/-- The `inputs` signature with every name that collides with a `reference`-key
    removed. Used to force disjointness of the three signature blocks (in-out,
    input-only, output-only): filtering by the union of the already-committed
    blocks' keys guarantees the surviving block shares no key with them.
    `disjointInputs [] reference = []` and, when `inputs` is already disjoint from
    `reference.keys`, `disjointInputs inputs reference = inputs`. -/
def disjointInputs (inputs : ListMap (Identifier Unit) LMonoTy)
    (reference : ListMap (Identifier Unit) LMonoTy) : ListMap (Identifier Unit) LMonoTy :=
  inputs.filter (fun p => !(ListMap.keys reference).contains p.1)

/-- The `old`-scope variable context for an in-out block `M`: each in-out
    parameter `(g, ty)` contributes an entry `(old g, ty)`. This is the value-level
    counterpart of the declarative `procBodyContext`'s `oldScope` (which further
    wraps each type as a trivial polytype); seeding the body's `VarCtx` with these
    bindings lets the body *read* the entry value `old g` of each in-out
    parameter, exactly as a postcondition may. `CoreIdent.mkOld` prefixes the
    (space-containing) marker `"old "`, so no `old`-key can collide with a
    generated parameter name. -/
def oldVars (M : ListMap (Identifier Unit) LMonoTy) : ListMap (Identifier Unit) LMonoTy :=
  M.map (fun (id, ty) => (CoreIdent.mkOld id.name, ty))

/-- Generate a labeled contract clause list (`preconditions` or `postconditions`):
    a `ListMap` from label names to `Procedure.Check`s, each wrapping a `bool`
    expression drawn from `genLExpr … .bool`. Labels come from `genNameList`; the
    `attr`/`md` fields are left at their defaults (`.Default` / `#[]`).

    Every generated clause is a well-typed `bool` expression in the *empty* bvar
    context, so it satisfies both `preconditionsTyped` and `postconditionsTyped`
    under the annotated typing spec (which ignores the ambient context). -/
def genChecks [Gen G] (octx : OpCtx) (tvars : List TyIdentifier) (depth : Nat) :
    G (ListMap CoreLabel Procedure.Check) := do
  let labels ← genNameList depth
  labels.mapM (fun l => do
    let e ← genLExpr [] octx [] tvars [] depth .bool
    pure (l, ({ expr := e } : Procedure.Check)))

/-- Generate a well-typed `Procedure`.

    - `typeArgs` — a `Nodup` list of type-variable names (via `genTypeArgs`).
    - `outputs`  — a `Nodup`-keyed signature with types over `typeArgs` (via
      `genInputs typeArgs size`).
    - `inputs`   — a `Nodup`-keyed signature with types over `typeArgs` (via
      `genInputs typeArgs size`), filtered by `disjointInputs` to be disjoint
      from the output keys (so no in-out parameters).
    - `preconditions` / `postconditions` — labeled `bool` expressions over
      `typeArgs` (via `genChecks`).
    - `body`     — a `structured` list of up to `len` statements, each generated
      at element size `size`, threaded from the inputs **and** outputs as the
      initial variable scope (so `set`s and control-flow guards may reference
      either), with the *inputs'* keys marked immutable so the body may read but
      never assign to them.

    `noFilter` / statement `MetaData` are at their defaults.

    See `genProcedure_sound` for the well-typedness guarantee. -/
def genProcedure [Gen G] (octx : OpCtx) (size len : Nat) : G Procedure := do
  let name ← genIdentName
  let typeArgs ← genTypeArgs size
  -- Three mutually-disjoint signature blocks. `M` is the in-out block (parameters
  -- that appear in *both* `inputs` and `outputs`); `I` is input-only; `O` is
  -- output-only. Disjointness is forced by filtering each later block by the
  -- keys already committed (`disjointInputs`), so all three share no key.
  let inout ← genInputs typeArgs size
  let rawInputOnly ← genInputs typeArgs size
  let inputOnly := disjointInputs rawInputOnly inout
  let rawOutputOnly ← genInputs typeArgs size
  let outputOnly := disjointInputs rawOutputOnly (inout ++ inputOnly)
  -- Front-aligned layout: the shared in-out block leads both signatures, so the
  -- call-site argument positions line up.
  let inputs := inout ++ inputOnly
  let outputs := inout ++ outputOnly
  let preconditions ← genChecks octx typeArgs size
  let postconditions ← genChecks octx typeArgs size
  -- Seed the body's variable scope with the inputs, outputs, and the `old`
  -- bindings of the in-out block (`old g` for each `g ∈ M`) — mirroring the
  -- declarative `procBodyContext`. The inputs *and* the `old` bindings are marked
  -- immutable, so the only writable keys are the output-only names (`O`), which
  -- are exactly the outputs the body is entitled to assign. `VarCtx` and
  -- `LMonoTySignature` are both `List ((Identifier Unit) × LMonoTy)`.
  let (body, _, _) ← genStmts [] octx typeArgs
    (ListMap.keys inputs ++ ListMap.keys (oldVars inout)) []
    (LContext.default) (inputs ++ outputs ++ oldVars inout) size len
  pure {
    header := {
      name := ⟨name, ()⟩,
      typeArgs := typeArgs,
      inputs := inputs,
      outputs := outputs,
      noFilter := false
    },
    spec := {
      preconditions := preconditions,
      postconditions := postconditions
    },
    body := .structured body
  }

-- ── Quick tests ──────────────────────────────────────────────────────────

open Std in
instance instToFormatUnitProcedureHasTypeAGen : ToFormat Unit where
  format _ := .nil

-- Smoke test: a handful of procedures at size 2, up to 4 body statements.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let p ← genProcedure [] 2 4
  IO.println <| Std.format p.header |>.pretty : IO Unit)

end StrataGenerators.Procedure
