-- Only the *executable* statement generator is needed here (`genStmtChain`), not its
-- proofs: importing the proof module `StmtHasTypeAGen` would pull in Mathlib and
-- so make this file unimportable alongside Strata's transform passes (`List.Forall₂`
-- is defined by both Strata and Batteries). Keeping to `.Core` preserves the
-- repo-wide "Core.lean = code, sibling = proofs" split and is what lets
-- `ProcedureHasTypeAGen/TestSupport.lean` exist. The proof file
-- (`ProcedureHasTypeAGen.lean`) still sees the statement proofs via `Support.lean`.
import StrataGenerators.StmtHasTypeAGen.Core
import Strata.Languages.Core.Procedure

open Lambda LExpr RandomChoice Core Imperative ArbString Std
-- This file does *not* open `StrataGenerators.Function`. The proof file `FunctionHasTypeAGen.lean` introduces
-- that namespace, and nothing here needs it. The *code* of the generator for a function that this file uses,
-- which is `genIdentName`, `genTypeArgs` and `genInputs`, is at the top level of
-- `FunctionHasTypeAGen/Core.lean`.
open StrataGenerators.Stmt

/-!
# Core generator definition for well-typed Strata Core `Procedure`s

This file defines `genProcedure`, a generator of well-typed Strata Core
procedures (`Procedure`) satisfying the `ProcHasTypeA` relation of
`Strata.Languages.Core.ProcedureTypeSpec`.

## Design: in-out parameters via three disjoint signature blocks

`ProcHasType'` has eight obligations (see `ProcHasType'`). The generator produces:

- The type arguments are a list of type-variable names that holds no duplicate, from `genTypeArgs`, exactly as
  in `genFunction`. That list discharges the field about distinct type arguments. `genLMonoTy typeArgs` draws
  each input type and each output type over those type arguments, so the field about an undeclared variable
  holds.
- Three signature blocks whose keys are disjoint in pairs. `genInputs typeArgs` gives each of them with distinct
  keys, and the filter `disjointInputs` makes them disjoint:
  * The in-out block holds each parameter that has *both* roles.
  * The input-only block holds each parameter with the input role only, and the filter makes its keys disjoint
    from the keys of the in-out block.
  * The output-only block holds each parameter with the output role only, and the filter makes its keys disjoint
    from the keys of the other two blocks.

  The shared in-out block comes first in both signatures, so the shared parameters take the same first positions
  in both lists. So `getInoutParams = M` (the shared block), discharging
  `inputsNodup`/`outputsNodup` (each is an append of two disjoint `Nodup`-keyed
  blocks).
- The preconditions and the postconditions are labelled expressions of the type `bool`, from `genChecks`.
  **Both** obligations reduce, under the annotated specification, whose `exprTyped` reads no context, to
  `HasTypeA [] c.expr bool`. That is exactly what `genLExpr … .bool` gives, so neither obligation depends on the
  context of the inputs or of the body.
- The body is a `structured` list of statements. Its length is not more than the given length, and its initial
  scope holds the inputs, the outputs and the old bindings of the in-out block. That scope follows the
  declarative `procBodyContext`, whose scope for a body holds the scope of the inputs, of the outputs and of
  oldScope`) and with `inputs.keys ++ (oldVars M).keys` as the immutable names.
  The body may therefore freely *read* the inputs and the `old` bindings but can
  only *assign* to the output-only names `O` (`set` targets are drawn from the
  mutable sub-context, which excludes the immutable inputs and `old` bindings).
  This discharges `bodyTyped` (via `procBodyContext_inout`, which identifies the
  body context with `procToTCtx (inputs ++ outputs ++ oldVars M)`) and `modRights`
  (via `genStmtChain_mutableVars`, whose write-target tracking is over the mutable
  keys, i.e. exactly the output-only keys `O ⊆ outputs.keys`).

The invariant that the soundness proof threads is the `Functional` predicate, and not the one about distinct
keys. The in-out block occurs in the inputs and in the outputs, at the *same* type, so the seed holds a
duplicate key. The two entries agree on their values. A key of an old binding holds a space, and each generated
parameter name holds no space, which `genIdentName_no_space` proves. Therefore no such key collides with a
parameter name.

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

/-- Project a parameter signature to the expression-layer `FVarCtx` a contract
    clause reads its free variables from. Each entry of the signature becomes an entry of that context.

    This definition has a name, and it is not inline at each call site of `genChecks`. Therefore it stays *folded*
    when a proof unfolds the support of `genProcedure`, and each proof about a precondition and about a
    postcondition matches against it syntactically. An inline form would instead force an expensive expansion of
    the projection term. -/
def sigFctx (sig : @LMonoTySignature Unit) : FVarCtx :=
  sig.map (fun p => (p.1.name, p.2))

/-- Generate a labeled contract clause list (`preconditions` or `postconditions`):
    a `ListMap` from label names to `Procedure.Check`s, each wrapping a `bool`
    expression drawn from `genLExpr … .bool`. Labels come from `genNameList`; the
    `attr`/`md` fields are left at their defaults (`.Default` / `#[]`).

    Every generated clause is a well-typed `bool` expression in the *empty* bvar
    context, so it satisfies both `preconditionsTyped` and `postconditionsTyped`
    under the annotated typing spec (which ignores the ambient context). -/
def genChecks [Gen G] (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (depth : Nat) (pctx : PolyOpCtx := []) : G (ListMap CoreLabel Procedure.Check) := do
  let labels ← genNameList depth
  labels.mapM (fun l => do
    let e ← genLExpr fctx octx pctx tvars [] depth .bool
    pure (l, ({ expr := e } : Procedure.Check)))

/-- Generate a well-typed `Procedure`.

    - The type arguments are a list of type-variable names with no duplicate, from `genTypeArgs`.
    - The outputs are a signature with distinct keys, whose types are over the type arguments, from
      `genInputs typeArgs size`.
    - The inputs are a signature with distinct keys, whose types are over the type arguments, from
      `genInputs typeArgs size`. The filter `disjointInputs` makes its keys disjoint from the keys of the
      outputs, so this call gives no in-out parameter.
    - The preconditions and the postconditions are labelled expressions of the type `bool` over the type
      arguments, from `genChecks`.
    - The body is a `structured` list of statements. Its length is not more than the given length, the generator
      makes each element at the given size, and the initial scope holds the inputs **and** the outputs. Therefore
      a `set` command and a guard can name
      either), with the *inputs'* keys marked immutable so the body may read but
      never assign to them.

    - The context of the callable procedures holds the signature of each procedure that the body can call. Each
      entry records the in-out block, the input-only block and the output-only block, with the shared block first
      in both roles.
      Threaded into `genStmtChain` so the body may emit `call` statements against
      them, and an empty context gives a body with no call. The generated body is sound against each program for
      which `ProcSigCorresponds procs P` holds. Read `genProcedure_sound`.

    `noFilter` / statement `MetaData` are at their defaults.

    The body is generated under the *ambient* context `C` (its type parameters
    marked rigid) rather than a hardcoded `LContext.default`, so a caller can thread
    in the context under which the surrounding program is being checked; the ambient
    type-scope `Γ` is likewise threaded to the soundness statement (see
    `genProcedure_sound`). Passing `LContext.default` and `{}` recovers the old
    behaviour.

    See `genProcedure_sound` for the well-typedness guarantee. -/
def genProcedure [Gen G] (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (_Γ : TContext Unit) (size len : Nat)
    (pctx : PolyOpCtx := []) : G Procedure := do
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
  -- The shared in-out block `M` leads both signatures (`inputs = M ++ I`,
  -- `outputs = M ++ O`), so the shared parameters occupy the same leading
  -- positions in both and the call-site argument positions line up.
  let inputs := inout ++ inputOnly
  let outputs := inout ++ outputOnly
  -- The contract clauses may *read* parameters, so each is generated at the
  -- free-variable context the declarative spec types it in (`ProcedureTypeSpec`):
  --   * preconditions see the **inputs** only (`procInputContext`);
  --   * postconditions see **inputs ++ outputs ++ old(inout)** (`procBodyContext`).
  -- A signature entry `(⟨x, ()⟩, τ)` becomes the `FVarCtx` entry `(x, τ)`.
  let preconditions ← genChecks (sigFctx inputs) octx typeArgs size pctx
  let postconditions ←
    genChecks (sigFctx (inputs ++ outputs ++ oldVars inout)) octx typeArgs size pctx
  -- The scope of the body starts with the inputs, the outputs, and the old binding of each entry of the in-out
  -- block. That scope follows the declarative `procBodyContext`. The inputs *and* each old binding are immutable,
  -- so the writable keys are the output-only names, which
  -- are exactly the outputs the body is entitled to assign. `VarCtx` and
  -- `LMonoTySignature` are both `List ((Identifier Unit) × LMonoTy)`.
  --
  -- Body expressions draw their free variables from the *current* scope: the
  -- each statement generator computes its context of the free variables from the scope at each step, through
  -- `VarCtx.toFVarCtx`. Therefore an expression of a generated body can *read* a parameter, including one whose
  -- type is polymorphic, and it can read each local that an earlier statement declares. It does not only declare
  -- a fresh local. Each emitted free variable is in the current scope, so a name that a fresh `init` gives never
  -- collides with
  -- them (the `init_det` rule's `x ∉ getVars e` premise), which is what keeps the
  -- generator sound (see `freshNamesDisjointFromExprs_toFVarCtx`).
  let (body, _, _) ← genStmtChain octx typeArgs
    (ListMap.keys inputs ++ ListMap.keys (oldVars inout)) procs []
    -- The procedure's type parameters are *rigid* inside its body: unification
    -- must not refine them (a caller may instantiate them at any type), so the
    -- body is generated under a context marking `typeArgs` rigid. This matches
    -- `Procedure.typeCheck`, which sets `rigidTypeVars` to the type parameters
    -- before checking the body, and pins a generated `init`'s stored type to its
    -- annotation (see `genProcedure_complete` / the statement-level `hRigid`).
    ({ C with rigidTypeVars := typeArgs }) (inputs ++ outputs ++ oldVars inout) pctx size len
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

/-- Read the `ProcSig` of a procedure header off its signature, under a
    caller-chosen name `name` (the post-relabel `P{i}` a call site refers to). The
    three blocks are recovered exactly as `genProcedure` lays them out:

    * `getInoutParams` gives the in-out block, whose keys the inputs and the outputs share.
    * The input-only block holds each input whose key is *not* an output key.
    * `getOutputOnlyParams` gives the output-only block, which holds each output whose key is *not* an input key.

    For a header that `genProcedure` gives, where the inputs are the shared block and then the input-only block,
    the outputs are the shared block and then the output-only block, and the keys of the three blocks are
    disjoint in pairs, this function recovers the three blocks exactly. Therefore
    `ProcSigCorresponds [headerProcSig name h] P` holds for a monomorphic procedure of that header and that name.
    That is why each harness gives the signature of an already generated **monomorphic** procedure only to a
    later body. Read `TestScaffold.genProcsG`. -/
def headerProcSig (name : String) (h : Procedure.Header) : ProcSig where
  pname := name
  typeArgs := h.typeArgs
  M := h.getInoutParams
  I := h.inputs.filter (fun p => !(ListMap.keys h.outputs).contains p.1)
  O := h.getOutputOnlyParams

-- ── Quick tests ──────────────────────────────────────────────────────────

open Std in
instance instToFormatUnitProcedureHasTypeAGen : ToFormat Unit where
  format _ := .nil

-- Smoke test: a handful of procedures at size 2, up to 4 body statements.
#guard_msgs(drop warning, drop all) in
#eval (for _ in [:5] do
  let p ← genProcedure [] [] LContext.default {} 2 4
  IO.println <| Std.format p.header |>.pretty : IO Unit)

end StrataGenerators.Procedure
