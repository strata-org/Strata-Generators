import Strata.Languages.Core.StatementTypeSpec
import StrataGenerators.CmdHasTypeAGen.Core

open Lambda Core Imperative

/-!
# Definitions of the call generator

The signature records the statement generator draws call targets from, their correspondence with
the procedures of a program, and the argument lists and declarations a generated call is built
from.
-/

namespace StrataGenerators.Stmt

-- ── Procedure-signature context (call targets) ────────────────────────────

/-- A callee's signature description, stored *directly* with the shared in-out block leading both
    roles. This layout is not automatic for an arbitrary `P`-procedure; it is what `genProcedure`
    emits and what a call site must respect. `M` = in-out block, `I` = input-only block, `O` =
    output-only block, so `inputs = M ++ I` and `outputs = M ++ O`.

    The field `typeArgs` holds the **own** type parameters of the callee. A call site instantiates
    them with a concrete substitution, which is the existential of the `CmdExtHasType'.call` rule.
    Therefore the types that the caller must give for an argument and for a target are the
    *instantiated* blocks, such as `substSig σ M`. This structure stores each declared block over
    its type parameters, with no instance, and `substSig` applies the substitution when a proof
    needs it. An empty list of type parameters gives the monomorphic case, where the substitution is
    empty and `substSig` is the identity. -/
structure ProcSig where
  /-- The callee's name (matched against `Program.Procedure.find?`). -/
  pname : String
  /-- The callee's own type parameters (empty for a monomorphic callee). -/
  typeArgs : List TyIdentifier
  /-- The in-out (mutable) parameter block. -/
  M : @LMonoTySignature Unit
  /-- The input-only parameter block. -/
  I : @LMonoTySignature Unit
  /-- The output-only parameter block. -/
  O : @LMonoTySignature Unit

/-- A procedure with an empty signature, so that `ProcSig` is `Inhabited`. `elements` and its lemma
    about the inversion of a support need that instance inside `genCallStmt`. -/
instance : Inhabited ProcSig := ⟨⟨"", [], [], [], []⟩⟩

/-- Instantiate a parameter block's *types* by a substitution `σ`, leaving the
    parameter *names* untouched. Used to turn a callee's declared (over-`typeArgs`)
    block into the concrete block a call site must satisfy under the chosen
    instantiation `σ`. The call rule substitutes with `[σ]` (a single-scope
    substitution), so `substSig` does likewise. -/
def substSig (σ : List (TyIdentifier × LMonoTy)) (block : @LMonoTySignature Unit) :
    @LMonoTySignature Unit :=
  block.map (fun p => (p.1, LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) p.2))

/-- `substSig` preserves keys (it only rewrites types). -/
@[simp] theorem substSig_keys (σ : List (TyIdentifier × LMonoTy))
    (block : @LMonoTySignature Unit) : (substSig σ block).keys = block.keys := by
  simp only [substSig, ListMap.keys_eq_map_fst, List.map_map, Function.comp_def]

/-- `substSig` preserves length. -/
@[simp] theorem substSig_length (σ : List (TyIdentifier × LMonoTy))
    (block : @LMonoTySignature Unit) : (substSig σ block).length = block.length :=
  List.length_map ..

/-- The values of an instantiated block are the pointwise `subst [σ]` of the
    declared values. -/
theorem substSig_values (σ : List (TyIdentifier × LMonoTy))
    (block : @LMonoTySignature Unit) :
    (substSig σ block).values =
      block.values.map (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ])) := by
  simp only [substSig, ListMap.values_eq_map_snd, List.map_map, Function.comp_def]

/-- `substSig` distributes over block append. -/
theorem substSig_append (σ : List (TyIdentifier × LMonoTy))
    (a b : @LMonoTySignature Unit) :
    substSig σ (a ++ b) = substSig σ a ++ substSig σ b :=
  List.map_append ..

/-- Pointwise key access commutes with `substSig` (keys are untouched). -/
theorem substSig_keys_getElem (σ : List (TyIdentifier × LMonoTy))
    (b : @LMonoTySignature Unit) (i : Nat) (h : i < (substSig σ b).keys.length)
    (h' : i < b.keys.length) : (substSig σ b).keys[i]'h = b.keys[i]'h' := by
  simp only [substSig_keys]

/-- Pointwise value access commutes with `substSig` via `subst [σ]`. -/
theorem substSig_values_getElem (σ : List (TyIdentifier × LMonoTy))
    (b : @LMonoTySignature Unit) (i : Nat) (h : i < (substSig σ b).values.length)
    (h' : i < b.values.length) :
    (substSig σ b).values[i]'h =
      LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (b.values[i]'h') := by
  simp only [substSig_values, List.getElem_map]

/-- At the empty instantiation, `substSig` is the identity. A substitution with one empty scope
    fixes each monotype, so both the name and the type of an entry stay the same. That fact makes
    the monomorphic path a definitional special case of the polymorphic one. -/
@[simp] theorem substSig_nil (block : @LMonoTySignature Unit) :
    substSig [] block = block := by
  simp only [substSig]
  rw [show (fun p : Identifier Unit × LMonoTy =>
        (p.1, LMonoTy.subst (Strata.Util.HMaps.ofScopes [[]]) p.2)) = id from by
    funext p
    -- `ofScopes [[]]` is the single empty scope, and `subst` over it is the identity.
    simp only [id_eq, Strata.Util.HMaps.ofScopes, List.map_cons, List.map_nil,
      show Strata.Util.HMap.ofList ([] : List (TyIdentifier × LMonoTy))
        = Strata.Util.HMap.empty from rfl, LMonoTy.subst_single_empty],
    List.map_id]

/-- The set of callable procedures, each with its signature (shared in-out block
    leading both roles). -/
abbrev ProcSigCtx := List ProcSig

/-- The context describes each callable procedure of the program faithfully. Each entry names a
    procedure of the program whose type parameters are the ones that the entry records, and whose
    declared signature decomposes as the entry records, with the shared block at the front of the
    inputs and of the outputs. The keys of the input-only block are also disjoint from the keys of
    the two written-to blocks, and the keys of the outputs are distinct. Those are exactly the
    hypotheses that `call_mixed_body_sound` uses for the `.call` case, after the caller instantiates
    each block by the substitution that it chose.

    The callee can be **polymorphic**, which means that its list of type parameters is not empty.
    The call site then chooses a concrete instantiation, and it gives each argument and each target
    at the instance of the declared block. The condition about disjointness is stated over the
    *declared* keys, and `substSig` keeps each key. Therefore that condition also holds for each
    instantiated block. -/
def ProcSigCorresponds (procs : ProcSigCtx) (P : Program) : Prop :=
  ∀ s ∈ procs, ∃ proc, Program.Procedure.find? P s.pname = some proc ∧
    proc.header.typeArgs = s.typeArgs ∧
    proc.header.inputs = s.M ++ s.I ∧
    proc.header.outputs = s.M ++ s.O ∧
    (∀ i (hi : i < s.I.keys.length), (s.M ++ s.O).keys.contains (s.I.keys[i]'hi) = false) ∧
    (s.M ++ s.O).keys.Nodup

/-- **The correspondence in the other direction, for completeness.** `ProcSigCorresponds` says that
    each callee of the context resolves in the program, which is what *soundness* needs, because a
    generated call must be well typed. This predicate says the reverse: the context *holds* each
    procedure of the program whose signature admits the decomposition into the three blocks. That is
    what *completeness* needs, because a well-typed call must be reachable. The entry also records
    the type parameters of the procedure, so that a call site can instantiate them. -/
def ProcSigComplete (procs : ProcSigCtx) (P : Program) : Prop :=
  ∀ pname proc typeArgs M I O,
    Program.Procedure.find? P pname = some proc →
    proc.header.typeArgs = typeArgs →
    proc.header.inputs = M ++ I →
    proc.header.outputs = M ++ O →
    (∀ i (hi : i < I.keys.length), (M ++ O).keys.contains (I.keys[i]'hi) = false) →
    ∃ s ∈ procs, s.pname = pname ∧ s.typeArgs = typeArgs ∧ s.M = M ∧ s.I = I ∧ s.O = O

/-- Merge two lists under a Boolean mask, and keep the relative order inside each
    list. `true` takes the next element of `xs`, and `false` takes the next element
    of `ys`. When the mask ends, or when the chosen list is empty, the rest of both
    lists follows.

    The mask reaches *exactly* the order-preserving interleavings of `xs` and `ys`:
    `mergeBy_surjective` gives every one of them, `mergeBy_interleave` gives no more
    than them, and `exists_mask_iff_interleave` is the two together. -/
def mergeBy {α : Type} : List Bool → List α → List α → List α
  | [], xs, ys => xs ++ ys
  | true :: bs, x :: xs, ys => x :: mergeBy bs xs ys
  | true :: bs, [], ys => mergeBy bs [] ys
  | false :: bs, xs, y :: ys => y :: mergeBy bs xs ys
  | false :: bs, xs, [] => mergeBy bs xs []

/-- Build the call arguments for a callee whose signature decomposes as `inputs = M ++ I`,
    `outputs = M ++ O` (`M` = in-out, `I` = input-only, `O` = output-only, the shared block `M`
    leading both). The in-out block leads (as `inoutArg` nodes, so each is a pass-by-reference
    variable named exactly `M.keys[i]`, as the call rule's in-out premise requires). Then come the by-value
    inputs `exprs` (as `inArg` nodes) and the output-only *targets* `T` (as `outArg` nodes), merged
    under the mask `mask`. This layout makes the argument positions line up with the parameter
    positions the callee declares. Read `getIn_mkArgs` and `getLhs_mkArgs`.

    **Why `mask` exists.** The `call` rule constrains the input positions and the write positions
    one at a time, through `CallArg.getInputExprs` and `CallArg.getLhs`. Each of those drops the
    other kind of node, so the rule leaves the relative order of an `inArg` and an `outArg` free.
    `mask` gives the generator that same freedom, so a call such as `call p(out y, 1);` is
    reachable. The in-out block still has to lead: `M` heads both projections, so an `inoutArg`
    after an `inArg` or after an `outArg` would break the positional match.

    `T` is a **separate** argument rather than the callee's own `O`, because the Core spec does not
    constrain an out argument's *name*: any writable variable of the declared type will do. `T` is
    therefore a caller-chosen list of receiving variables, required only to be as long as `O` and to
    match it *by position in its type*. Read `outTargets`, which is the choice of the generator, and
    the premise `hTinΓ` of each call soundness theorem, which pairs the name of a target with the
    type that the callee declares at that position. -/
def mkArgs (M T : @LMonoTySignature Unit) (exprs : List Expression.Expr)
    (mask : List Bool) : List (CallArg Expression) :=
  M.map (fun p => CallArg.inoutArg p.1) ++
    mergeBy mask (exprs.map CallArg.inArg) (T.map (fun p => CallArg.outArg p.1))

/-- The statement list `var x₁ : mty₁ := *; … ; var xₙ : mtyₙ := *` that
    declares every `(x, mty) ∈ news` (nondeterministically, so no initializer
    expression is required). -/
def initChain (news : List (Identifier Unit × LMonoTy)) : List Statement :=
  news.map (fun p => Statement.init p.1 (.forAll [] p.2) .nondet default)

/-- The flat `VarCtx` analogue of `insertAll`: the *generator-side* scope after running
    `initChain news` in the ambient scope. Because the chain is emitted **inline** (not inside a block), these
    declarations genuinely escape into the enclosing sequence. Therefore this definition, and not
    `ctx`, gives the output scope of the call. `toTCtx_insertAllCtx` (in `StmtHasTypeAGen.lean`)
    relates it to `insertAll`. -/
def insertAllCtx (ctx : VarCtx) (news : List (Identifier Unit × LMonoTy)) : VarCtx :=
  news.foldl (fun ctx p => Map.insert ctx p.1 p.2) ctx

end StrataGenerators.Stmt
