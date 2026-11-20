import StrataGenerators.StmtHasTypeAGen.Core
import StrataGenerators.CmdHasTypeAGen
import StrataGenerators.FunctionHasTypeAGen
import StrataGenerators.HasTypeAGen.OpsConsistentBridge
import StrataGenerators.StmtHasTypeAGen.GenCallStmtSound

open Lambda LExpr RandomChoice Core Imperative TypeSpec ArbString
open StrataGenerators.Stmt
open StrataGenerators.AnnotFacts (ExprCtxOk genLExpr_exprWellTyped)

/-!
# Soundness and completeness of `genStmt` / `genStmtChain`

`genStmt` / `genStmtChain` (in `StmtHasTypeAGen/Core.lean`) generate random Strata
Core statements. This file proves them **sound** with respect to the typing relations
`StatementWellTyped` / `StatementsWellTyped` of
`Strata.Languages.Core.Typing.Spec.TypingSpec`, and gives the membership lemmas that the
completeness proofs use.

## Compositional structure

The proofs are *compositional*: they reuse the soundness of the component generators rather than
reproving anything about expressions, commands, or functions.

- **Commands** (`cmd` constructor): reuse `genCmd_sound_env` (from `CmdHasTypeAGen.lean`). A
  generated imperative command wrapped as `CmdExt.cmd` is typed by `CmdExtWellTyped.cmd`.
- **Expressions** (guards, measures, invariants): reuse `genLExpr_exprWellTyped`, at the
  free-variable context of the scope, exactly as the command generator does.

## The single `size` budget

`genStmt`/`genStmtChain` take a single `size` (the QuickCheck-style `sized` knob):
there is no separate `fuel` for the nesting. The parameter `size` bounds the depth of the nesting *and* the
size of an expression and the length of a generated statement sequence, because each sub-generator for a leaf
and for an expression receives it. As a statement nests, `size` shrinks, so the leaf/expression
sub-generators are invoked at *varying* depths. Consequently the soundness environment
(`GenStmtSoundEnv`) is **depth-generic**.

## Threading

Both proofs thread three contexts, mirroring the generator:
- the variable scopes are threaded via a `VarCtx` and related to the semantic `TContext` through a
  `toTCtx`/`VarCtxCorresponds` bundle (`GenStmtSoundEnv`), just as `genCmds` does;
- `C` is threaded as an honest `LContext CoreLParams`; the generator's output
  `outC` field *is* the output ambient context of the typing relation;
- `L` (the enclosing-block labels, `labels`) is threaded as a `List String`. The `exit label`
  rule requires `label ∈ L`, which the `elements` support of `genExitStmt` discharges.
-/

namespace StrataGenerators.Stmt

open StrataGenerators.Function

-- ── Soundness environment ────────────────────────────────────────────────

/-- A soundness environment for the statement generator, bundling the context-dependent facts
    about scopes needed to type every constructor. It packages the `genCmd` soundness data
    (`toTCtx`, `corr`, `freshDisjoint`, `toTCtx_insert`).

    The freshness fact is quantified over **all** depths `d`: because the single `size` budget
    shrinks as statements nest, a generated command or expression may be produced at any depth.

    None of the fields mention a specific `C`, so the same environment types
    statements at *every* ambient context reached while threading a sequence. -/
structure GenStmtSoundEnv (octx : OpCtx) (tvars : List TyIdentifier)
    (pctx : PolyOpCtx := []) where
  /-- Produce the semantic `TContext` for any flat `VarCtx`. -/
  toTCtx : VarCtx → TContext Unit
  /-- The `VarCtx ↔ TContext` correspondence holds for every context. -/
  corr : ∀ ctx, VarCtxCorresponds ctx (toTCtx ctx)
  /-- A fresh name never collides with a free variable of a generated expression, at each depth.
      The condition holds at each context, because the generator draws each free variable from
      `ctx.toFVarCtx`, whose names are the names of `ctx`, and a fresh name differs from each name
      of `ctx`. -/
  freshDisjoint :
    ∀ d (ctx : VarCtx), FreshNamesDisjointFromExprs ctx.toFVarCtx octx tvars ctx d pctx
  /-- `toTCtx` commutes with `VarCtx.insert`, up to `TContext.Equiv`. The case for an `init`
      command needs that fact. An equality is not available, because a scope is a hash map. Read
      `GenCmdSoundEnv.toTCtx_insert`. -/
  toTCtx_insert : ∀ ctx (x : Identifier Unit) mty,
    TContext.Equiv (T := CoreLParams) (toTCtx (ctx.insert x mty))
      { toTCtx ctx with types := (toTCtx ctx).types.insert x (.forAll [] mty) }

/-- Reinterpret a `GenStmtSoundEnv` as a `GenCmdSoundEnv` at an arbitrary ambient context `C`
    and depth `d`. No `GenCmdSoundEnv` field references `C`, and the environment supplies its
    freshness fact at every depth. -/
def GenStmtSoundEnv.toCmdEnv {octx tvars pctx}
    (env : GenStmtSoundEnv octx tvars pctx) (C : LContext CoreLParams) (d : Nat) :
    GenCmdSoundEnv octx tvars d C pctx where
  toTCtx := env.toTCtx
  corr := env.corr
  freshDisjoint := fun ctx => env.freshDisjoint d ctx
  toTCtx_insert := env.toTCtx_insert

/-- `toTCtx` commutes with a *whole* `init` chain, not just one insertion: the
    generator-side `insertAllCtx` and the semantic `insertAll` are the same `foldl`,
    and `toTCtx_insert` matches them at each step. That fact is what lets the soundness lemmas
    for a call type the inline group of a call. -/
theorem GenStmtSoundEnv.toTCtx_insertAllCtx {octx tvars pctx}
    (env : GenStmtSoundEnv octx tvars pctx) (news : List (Identifier Unit × LMonoTy)) :
    ∀ ctx, Strata.Util.HMaps.Equiv
      (env.toTCtx (StrataGenerators.Stmt.insertAllCtx ctx news)).types
      (StrataGenerators.Stmt.insertAll (env.toTCtx ctx).types news) := by
  induction news with
  | nil => intro ctx; exact Strata.Util.HMaps.Equiv.refl _
  | cons hd tl ih =>
    intro ctx
    rw [StrataGenerators.Stmt.insertAllCtx_cons]
    -- Step past the head insertion with `toTCtx_insert`, then `insertAll` congruence for the
    -- tail.
    refine (ih _).trans ?_
    exact StrataGenerators.Stmt.insertAll_equiv tl (env.toTCtx_insert ctx hd.1 hd.2).1

/-- An expression that a statement generator draws from the scope `ctx` at a registered type is
    well-typed at that type in the variable scopes of `env.toTCtx ctx`, when the operators and
    schemes agree with `C`, the scope is functional and its types are well kinded in `C`. -/
theorem GenStmtSoundEnv.exprWellTyped {octx tvars pctx}
    (env : GenStmtSoundEnv octx tvars pctx) {C : LContext CoreLParams}
    (hops : ExprCtxOk C [] [] octx pctx) {ctx : VarCtx} (hFun : Map.Functional ctx)
    (hwk : ∀ ty ∈ ctx.values, C.WellKindedTy ty) {d : Nat} {τ : LMonoTy} {e : LExpr'}
    (hτ : LMonoTy.knownInstance τ C.knownTypes = true)
    (he : e ∈ SPMF.support (genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] d τ)) :
    ExprWellTyped C (env.toTCtx ctx).types e τ :=
  genLExpr_exprWellTyped (exprCtxOk_of_corresponds hops (env.corr ctx) hFun hwk) hτ he

-- ── Leaf-case soundness lemmas ───────────────────────────────────────────

variable {octx : OpCtx} {tvars : List TyIdentifier} {pctx : PolyOpCtx} {maxStmtSeqLen : Nat}
  {immutableVars : List (Identifier Unit)} {labels : List String}

-- ── The well-kindedness premise upstream's `init` rules impose ───────────
--
-- `CmdHasType'.init_det`/`init_nondet` require the stored monotype to be well-kinded in
-- the ambient context (`C.WellKindedTy`), i.e. every type constructor applied at the arity
-- `C.knownTypes` records for it. Two of the statement generators store types:
--
-- * `genCmdStmt`, whose `init` types come from `genLMonoTy`, and are therefore always
--   generable, so `SimpleTyArities C` suffices (`wellKindedTy_of_genLMonoTy`);
-- * `genCallStmt`, whose inline `init` chain stores the *callee's* signature types
--   instantiated by a sampled `σ`. Those depend on `procs`, `ctx` and `octx` rather than
--   on the generator alone.
--
-- `WellKindedOk` bundles what that needs, stated **directly** in
-- `LContext.WellKindedTy` rather than through the generator's type vocabulary.
-- The difference matters twice over:
--
-- * `WellKindedTy` is closed under each operation that a generator performs on a type of the context. Those
--   operations are `syntacticSubtypes`, `addNewTypes` and `LMonoTy.subst`, and
--   `generableTypesFromCtx_wellKinded` and `subst_wellKinded` prove the closure. Therefore the invariant has a
--   *proof* that each step keeps it, and no theorem assumes it. Read `wellKindedOk_preserved` below.
-- * Generability would be *false* at the level of a program. A generated `MutualDatatype`
--   block contributes constructor operators to `octx` whose types mention the datatype's
--   own `tcons`. Those types are well-kinded in the context that registers the block, but
--   the type generator cannot produce them.

/-- The well-kindedness discipline the statement generators need at an ambient context `C`
    and variable scope `ctx`: `C` registers the type constructors at their own
    arities (`genCmdStmt` draws its `init` types from `genLMonoTy`), and
    every type already recorded in the variable scope, the operator context, and a callable
    procedure's written-to blocks is well-kinded in `C`. -/
structure WellKindedAmbient (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) : Prop where
  /-- `C` registers `bool`/`int`/`string`/`real`/`regex` at 0, `arrow`/`Map` at 2 and
      `Sequence` at 1. This is enough to make every generable type well-kinded in `C`. -/
  arities : SimpleTyArities C
  /-- Every operator's type is well-kinded in `C`. Together with `ctxWK` this is what
      makes the call generator's sampled instantiations well-kinded (`generable`). -/
  octxWK : ∀ p ∈ octx.ops, C.WellKindedTy p.2
  /-- Each type of the in-out block and of the out-only block of a callable procedure is well-kinded in `C`.
      Those are the blocks that the call generator writes back through, and therefore also declares. -/
  sigsWK : ∀ s ∈ procs, ∀ ty ∈ (s.M ++ s.O).values, C.WellKindedTy ty

/-- `WellKindedAmbient` plus the scope-local half: every type currently in scope is
    well-kinded too. Split this way because only the scope-local half varies as a
    statement sequence runs; the ambient half is a property of `octx`/`procs`/`C` that
    the *caller* establishes once (see `genProcedure_sound`). -/
structure WellKindedOk (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) : Prop
    extends WellKindedAmbient octx procs C where
  /-- Every type in scope is well-kinded in `C`. -/
  ctxWK : ∀ ty ∈ ctx.values, C.WellKindedTy ty

/-- Each type that the call generator can sample for a type parameter of a callee is well-kinded in `C`. This
    lemma *derives* that fact from the two fields `ctxWK` and `octxWK`, because `generableTypesFromCtx` takes a
    syntactic subtype of a type of the context and the result type of an `arrow` only, and `C.WellKindedTy` is
    closed under both operations. -/
theorem WellKindedOk.generable {octx : OpCtx} {procs : ProcSigCtx}
    {C : LContext CoreLParams} {ctx : VarCtx} (h : WellKindedOk octx procs C ctx) :
    ∀ ty ∈ generableTypesFromCtx ctx.values [] octx, C.WellKindedTy ty :=
  generableTypesFromCtx_wellKinded ctx.values [] octx h.ctxWK (by simp) h.octxWK

/-- The `bool` fallback the call generator uses when nothing is generable is well-kinded. -/
theorem WellKindedOk.boolWK {octx : OpCtx} {procs : ProcSigCtx}
    {C : LContext CoreLParams} {ctx : VarCtx} (h : WellKindedOk octx procs C ctx) :
    C.WellKindedTy .bool :=
  genLMonoTy_mem_wellKindedTy (tvars := []) h.arities genLMonoTy_mem_bool

/-- `WellKindedAmbient` transports along an extension of the known-type table: nothing it
    asserts is disturbed by *adding* a type constructor name. -/
theorem WellKindedAmbient.mono {octx : OpCtx} {procs : ProcSigCtx}
    {C C' : LContext CoreLParams}
    (hmono : ∀ (n : String) (v : Nat), C.knownTypes[n]? = some v → C'.knownTypes[n]? = some v)
    (h : WellKindedAmbient octx procs C) : WellKindedAmbient octx procs C' :=
  { arities := simpleTyArities_mono hmono h.arities
    octxWK := fun p hp => wellKindedTy_mono hmono (h.octxWK p hp)
    sigsWK := fun s hs ty hty => wellKindedTy_mono hmono (h.sigsWK s hs ty hty) }

/-- A type built from the registered types of `C` is built from the registered types of every
    context that registers each type of `C` at the same arity. -/
theorem knownInstance_mono {C C' : LContext CoreLParams}
    (hmono : ∀ (n : String) (v : Nat), C.knownTypes[n]? = some v → C'.knownTypes[n]? = some v)
    {ty : LMonoTy} (h : LMonoTy.knownInstance ty C.knownTypes = true) :
    LMonoTy.knownInstance ty C'.knownTypes = true :=
  Lambda.LMonoTy.wellKinded_knownInstance ty C'.knownTypes
    (wellKindedTy_mono hmono (LMonoTy.knownInstance_wellKinded ty C.knownTypes h))

/-- `WellKindedOk` transports along an extension of the known-type table. -/
theorem WellKindedOk.mono {octx : OpCtx} {procs : ProcSigCtx}
    {C C' : LContext CoreLParams} {ctx : VarCtx}
    (hmono : ∀ (n : String) (v : Nat), C.knownTypes[n]? = some v → C'.knownTypes[n]? = some v)
    (h : WellKindedOk octx procs C ctx) : WellKindedOk octx procs C' ctx :=
  { h.toWellKindedAmbient.mono hmono with
    ctxWK := fun ty hty => wellKindedTy_mono hmono (h.ctxWK ty hty) }

/-- Every function name of `C` is in `functionNames C`. -/
theorem mem_functionNames {C : LContext CoreLParams} {s : String} (h : s ∈ C.functions) :
    s ∈ functionNames C := by
  have hmem := (Lambda.Factory.memIffMemNames C.functions s).mp h
  simpa only [functionNames, Array.mem_toList_iff] using hmem

/-- Every name in `functionNames C` is a function name of `C`. -/
theorem mem_functions_of_mem_functionNames {C : LContext CoreLParams} {s : String}
    (h : s ∈ functionNames C) : s ∈ C.functions :=
  (Lambda.Factory.memIffMemNames C.functions s).mpr
    (by simpa only [functionNames, Array.mem_toList_iff] using h)

/-- Soundness of `genCmdStmt` (at any depth `d`), when the operators and schemes agree with `C` and
    the scope is functional. -/
theorem genCmdStmt_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (C : LContext CoreLParams) (hops : ExprCtxOk C [] [] octx pctx) (ctx : VarCtx) (d : Nat)
    (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support (genCmdStmt (G := SPMF) octx tvars immutableVars C ctx d pctx)) :
    StatementsWellTyped P C (env.toTCtx ctx).types labels r.stmts r.outC
      (env.toTCtx r.outCtx).types := by
  revert r; show IsSoundFor _ _; rw [IsSoundFor.iff_obs, genCmdStmt]
  walk [(isSoundFor_self_support (genCmd _ _ _ _ _ _ _ _)).obs]
  exact StatementsWellTyped_singleton (.cmd C _ labels _ _ (.cmd _ _ _
    (genCmd_sound_env octx tvars immutableVars ctx d C pctx (env.toCmdEnv C d) hops hFun _ ‹_›)))

/-- Soundness of `genExitStmt`. With enclosing labels the target is drawn from
    them (`label ∈ L`, discharging the `exit` premise); with no enclosing block
    (`labels = []`) the generator is empty (support `∅`), so there is nothing to
    prove. -/
theorem genExitStmt_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (C : LContext CoreLParams) (ctx : VarCtx) (r : GenStmtResult)
    (hr : r ∈ SPMF.support (genExitStmt (G := SPMF) labels C ctx)) :
    StatementsWellTyped P C (env.toTCtx ctx).types labels r.stmts r.outC
      (env.toTCtx r.outCtx).types := by
  revert r; show IsSoundFor _ _; rw [IsSoundFor.iff_obs]; unfold genExitStmt; walk
  exact StatementsWellTyped_singleton (.exit C _ _ _ default _ ‹_› (Strata.Util.HMaps.Equiv.refl _))

/-- A name that starts with `localTypePrefix` is a local type name. -/
theorem isLocalTypeName_prefix_append (s : String) :
    isLocalTypeName (localTypePrefix ++ s) = true := by
  simp only [isLocalTypeName, String.startsWith_string_iff, String.toList_append]
  exact List.prefix_append _ _

/-- Every name `genLocalTypeName` draws is a local type name. -/
theorem genLocalTypeName_isLocal {s : String}
    (hs : s ∈ SPMF.support (genLocalTypeName (G := SPMF))) :
    isLocalTypeName s = true := by
  simp only [genLocalTypeName, mem_support_bind_iff, mem_support_pure_iff] at hs
  obtain ⟨d, _, rfl⟩ := hs
  split
  · assumption
  · exact isLocalTypeName_prefix_append d

/-- The name of every type constructor `genTypeConstructor` draws is a local type name. -/
theorem genTypeConstructor_isLocal {depth : Nat} {tc : TypeConstructor}
    (htc : tc ∈ SPMF.support (genTypeConstructor (G := SPMF) depth)) :
    isLocalTypeName tc.name = true := by
  simp only [genTypeConstructor, mem_support_bind_iff, mem_support_pure_iff] at htc
  obtain ⟨name, hname, _, _, _, _, rfl⟩ := htc
  exact genLocalTypeName_isLocal hname

/-- Soundness of `genTypeDeclStmt`, for a program `P` with no local type name among its type
    names. The declared name is a local type name, so it differs from every type name of `P`. -/
theorem genTypeDeclStmt_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (hLocalTypes : ∀ n ∈ programNamesOfKind P .type, ¬ isLocalTypeName n.name)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat) (r : GenStmtResult)
    (hr : r ∈ SPMF.support (genTypeDeclStmt (G := SPMF) C ctx d)) :
    StatementsWellTyped P C (env.toTCtx ctx).types labels r.stmts r.outC
      (env.toTCtx r.outCtx).types := by
  revert r; show IsSoundFor _ _; rw [IsSoundFor.iff_obs, genTypeDeclStmt]
  walk [(isSoundFor_self_support (genTypeConstructor _)).obs]
  have hfresh : ∀ n ∈ programNamesOfKind P .type, n.name ≠ _ :=
    fun n hn heq => hLocalTypes n hn (heq ▸ genTypeConstructor_isLocal ‹_›)
  exact StatementsWellTyped_singleton
    (.typeDecl C _ _ labels _ default _ hfresh ‹_› (Strata.Util.HMaps.Equiv.refl _))

-- ── Fresh-label freshness (for the `block` premise) ──────────────────────

/-- `fallbackFreshLabel labels` is absent from `labels`: it is strictly longer
    than every label in the list. Reuses the shared foldl-max bound
    `foldl_max_ge_of_mem` from `CmdHasTypeAGen/Core.lean` at `f := String.length`. -/
theorem fallbackFreshLabel_not_mem (labels : List String) :
    fallbackFreshLabel labels ∉ labels := by
  intro hmem
  have hlen : (fallbackFreshLabel labels).length =
      (labels.foldl (fun acc l => max acc l.length) 0) + 1 := by
    simp [fallbackFreshLabel, String.length_ofList, List.length_replicate]
  have hle := foldl_max_ge_of_mem String.length labels (fallbackFreshLabel labels) hmem 0
  omega

/-- Every label in the support of `genFreshLabel labels` is absent from `labels`,
    discharging the `label ∉ L` premise of the `block` typing rule. -/
theorem genFreshLabel_not_mem (labels : List String) :
    ∀ l, l ∈ SPMF.support (genFreshLabel (G := SPMF) labels) → l ∉ labels := by
  intro l hmem
  simp only [genFreshLabel, mem_support_bind_iff] at hmem
  obtain ⟨s, _, hl⟩ := hmem
  simp only [mem_support_ite_iff, mem_support_pure_iff] at hl
  rcases hl with ⟨_, rfl⟩ | ⟨hns, rfl⟩
  · exact fallbackFreshLabel_not_mem labels
  · exact hns

-- ── Procedure-call soundness ──────────────────────────────────────────────

/-! ### Reconciling the recipe with the call-soundness lemmas

`genCallStmt` inspects the in-out block `s.M` and the out-only block `s.O`
*separately* (that is the point of the recipe): it guards only on `s.M`, chooses
out-argument targets `T = outTargets … s.O` for itself, and concatenates two
`filter`s to get its init-list. The lemmas in `GenCallStmtSound.lean`, in
contrast, speak about the single
appended list `M ++ T` of variables the call writes to. The lemmas below are the
whole reconciliation: three facts about `outTargets` and two `append` fusions. -/

/-- `outTarget` never touches the *type* component: whichever variable it chooses,
    that variable carries the type the callee declares. -/
theorem outTarget_snd (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (base : Nat)
    (q : Identifier Unit × LMonoTy) (i : Nat) :
    (outTarget immutableVars ctx base q i).2 = q.2 := by
  simp only [outTarget]; split <;> rfl

/-- The values of a signature built by mapping a list are the second components of the images. -/
theorem listMap_values_map {α β γ : Type} (L : List γ) (f : γ → α × β) :
    ListMap.values (L.map f : ListMap α β) = L.map (fun x => (f x).2) := by
  induction L with
  | nil => rfl
  | cons x xs ih => exact congrArg ((f x).2 :: ·) ih

/-- **The out targets are positionally type-aligned with the callee's out block.**
    This is the `hTVals` premise every call-soundness lemma takes, and the only
    relation
    between the chosen targets `T` and the callee's declared out block `O` that the
    Core spec requires (out-argument *names* are the caller's to pick). -/
theorem outTargets_values (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (O : @LMonoTySignature Unit) (avoid : List String) :
    (outTargets immutableVars ctx O avoid).values = O.values := by
  refine (listMap_values_map _ _).trans ?_
  rw [ListMap.values_eq_map_snd (m := O)]
  refine (List.map_congr_left fun p _ => outTarget_snd ..).trans ?_
  exact (List.map_map ..).symm.trans (congrArg (List.map Prod.snd) (List.zipIdx_map_fst ..))

/-- One receiving variable per out-only parameter. -/
theorem outTargets_length (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (O : @LMonoTySignature Unit) (avoid : List String) :
    (outTargets immutableVars ctx O avoid).length = O.length := by
  simp only [outTargets, List.length_map, List.length_zipIdx]; rfl

/-- New out-argument names start past each name of the scope. -/
theorem maxNameLen_le_outNameBase (ctx : VarCtx) (avoid : List String) :
    maxNameLen ctx ≤ outNameBase ctx avoid :=
  Nat.le_add_right _ _

/-- **Every chosen out target is usable, unconditionally.** A target is either a
    `reusable` ambient variable (first disjunct) or a brand-new
    `indexedFreshName` past the longest name of `ctx`, which is fresh for `ctx` and hence
    `needsInit` (second disjunct). This is why the generator's guard need only
    mention the in-out block: an out-only parameter can never make a callee
    uncallable. -/
theorem outTargets_all_usableName (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (O : @LMonoTySignature Unit) (avoid : List String) :
    (outTargets immutableVars ctx O avoid).all (usableName immutableVars ctx) = true := by
  refine List.all_eq_true.mpr fun p hp => ?_
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  simp only [outTarget]
  split
  · rename_i h; simp [usableName, h]
  · simp [usableName, needsInit, freshOut,
      indexedFreshName_isFresh_of_le ctx (maxNameLen_le_outNameBase ctx avoid)]

/-- **When every out target is reused, the names to avoid play no role.** A target that is not
    reused is a new name, which has to be declared; so when no target has to be declared, each
    target is the callee's own variable, whatever the base of the new names. -/
theorem outTargets_eq_of_reused (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (O : @LMonoTySignature Unit) (avoid : List String)
    (h : (outTargets immutableVars ctx O []).filter (needsInit ctx) = []) :
    outTargets immutableVars ctx O avoid = outTargets immutableVars ctx O [] := by
  unfold outTargets
  apply List.map_congr_left
  intro q hq
  by_cases hre : reusable immutableVars ctx q.1 = true
  · simp only [outTarget, hre, ite_true]
  · exfalso
    have hmem : outTarget immutableVars ctx (outNameBase ctx []) q.1 q.2 ∈
        (outTargets immutableVars ctx O []).filter (needsInit ctx) := by
      refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
      simp only [outTarget, hre, Bool.false_eq_true, ite_false, needsInit, freshOut]
      exact indexedFreshName_isFresh_of_le ctx (maxNameLen_le_outNameBase ctx []) q.2
    rw [h] at hmem
    exact List.not_mem_nil hmem

/-- The check about the usability of an in-out name, over the whole write-list. Each out target needs no proof,
    which `outTargets_all_usableName` gives. -/
theorem all_usableName_append (immutableVars : List (Identifier Unit)) (ctx : VarCtx)
    (M O : @LMonoTySignature Unit) (avoid : List String)
    (hM : M.all (usableName immutableVars ctx) = true) :
    (List.append M (outTargets immutableVars ctx O avoid)).all (usableName immutableVars ctx)
      = true := by
  rw [List.all_eq_true]
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact List.all_eq_true.mp hM q h
  · exact List.all_eq_true.mp (outTargets_all_usableName immutableVars ctx O avoid) q h

/-- The recipe's per-block init-lists (in-out args first, then out targets), fused
    into one filter over `M ++ T`. -/
theorem filter_needsInit_append (ctx : VarCtx) (M T : @LMonoTySignature Unit) :
    (M.filter (needsInit ctx) ++ T.filter (needsInit ctx))
      = (List.append M T).filter (needsInit ctx) :=
  (List.filter_append ..).symm

/-- The generator's syntactic freshness filter (over the flat `VarCtx`) agrees with
    the semantic `missingIn` filter (over the variable scopes of the `TContext`). Both directions
    come from `VarCtxCorresponds`: fresh names are absent from `Γ`, and a bound
    `ctx` entry maps to a `some` in `Γ`. -/
theorem filter_needsInit_eq_missingIn (env : GenStmtSoundEnv octx tvars pctx)
    (ctx : VarCtx) (names : List (Identifier Unit × LMonoTy)) :
    names.filter (needsInit ctx)
      = StrataGenerators.Stmt.missingIn (env.toTCtx ctx).types names := by
  simp only [StrataGenerators.Stmt.missingIn]
  apply List.filter_congr
  intro q _
  simp only [needsInit]
  by_cases hfr : VarCtx.isFresh ctx q.1 = true
  · rw [(env.corr ctx).2 q.1 hfr]; simp [hfr]
  · -- not fresh ⇒ `ctx.find? = some τ` ⇒ `Γ.types.find? = some (∀[].τ)` ⇒ not `isNone`
    have hne : ctx.find? q.1 ≠ none := by
      intro h; exact hfr (by simp [VarCtx.isFresh, h])
    obtain ⟨τ, hτ⟩ := Option.ne_none_iff_exists'.mp hne
    rw [(env.corr ctx).1 q.1 τ hτ]
    simp [hfr]

/-- **Every argument-order mask is reachable.** `genCallTail` draws the mask from
    `listOf` over both Boolean values, whose support holds every finite `List Bool`.
    So the mask puts no restriction on which interleaving a call site can use. -/
theorem mem_support_argMask (mask : List Bool) :
    mask ∈ SPMF.support
      (listOf (elements [true, false] (by simp)) : SPMF (List Bool)) :=
  SPMF.mem_support_listOf_of_forall (fun b _ =>
    (mem_support_elements_iff (by simp)).mpr (by cases b <;> simp))

/-- **What a `genCallTail` result looks like.** A group in the support of `genCallTail` comes from
    the three guards holding, a list of inputs `exprs` that the input generator can draw at the
    instantiated input types and whose binder annotations are known, and an argument-order `mask`.
    The group is the `init` chain for the in-out names and out arguments that the scope lacks, then
    the call that `mkArgs` assembles, and the scope is extended by the declared names. -/
theorem genCallTail_support
    {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat} {s : ProcSig}
    {σ : List (TyIdentifier × LMonoTy)} {T : @LMonoTySignature Unit} {r : GenStmtResult}
    (hr : r ∈ SPMF.support
      (genCallTail (G := SPMF) octx tvars immutableVars C ctx d pctx s σ T)) :
    ((StrataGenerators.Stmt.substSig σ s.M).all (usableName immutableVars ctx) = true
      ∧ (StrataGenerators.Stmt.substSig σ s.M ++ T).keys.Nodup
      ∧ ((StrataGenerators.Stmt.substSig σ s.M).filter (needsInit ctx)).all
          (fun q => !(functionNames C).contains q.1.name) = true) ∧
    ∃ (exprs : List Expression.Expr) (mask : List Bool),
      List.Forall₂
        (fun e τ => e ∈ SPMF.support (genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] d τ))
        exprs (StrataGenerators.Stmt.substSig σ s.I).values ∧
      exprs.all (binderAnnotsKnownIn C.knownTypes) = true ∧
      r = ⟨StrataGenerators.Stmt.initChain
              ((StrataGenerators.Stmt.substSig σ s.M).filter (needsInit ctx)
                ++ T.filter (needsInit ctx))
            ++ [Statement.call s.pname (StrataGenerators.Stmt.mkArgs s.M T exprs mask) default],
          C, StrataGenerators.Stmt.insertAllCtx ctx
            ((StrataGenerators.Stmt.substSig σ s.M).filter (needsInit ctx)
              ++ T.filter (needsInit ctx))⟩ := by
  unfold genCallTail at hr
  dsimp only at hr
  split at hr
  · rename_i hg
    simp only [mem_support_bind_iff] at hr
    obtain ⟨exprs, hexprs, hr⟩ := hr
    split at hr
    · rename_i hgen
      simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨mask, _, rfl⟩ := hr
      exact ⟨hg, exprs, mask, (mem_support_mapM_iff _ _ exprs).mp hexprs, hgen, rfl⟩
    · simp only [mem_support_bot_iff] at hr
  · simp only [mem_support_bot_iff] at hr

/-- **Forward membership for `genCallTail`.** Under the three guards, inputs `exprs` that the input
    generator can draw at the instantiated input types and whose binder annotations are known, and
    any argument-order mask, the assembled group is in the support of `genCallTail`. This is the
    converse of `genCallTail_support`. -/
theorem genCallTail_mem
    {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat} {s : ProcSig}
    {σ : List (TyIdentifier × LMonoTy)} {T : @LMonoTySignature Unit}
    (hMusable : (StrataGenerators.Stmt.substSig σ s.M).all (usableName immutableVars ctx) = true)
    (hNodup : (StrataGenerators.Stmt.substSig σ s.M ++ T).keys.Nodup)
    (hMnotFn : ((StrataGenerators.Stmt.substSig σ s.M).filter (needsInit ctx)).all
      (fun q => !(functionNames C).contains q.1.name) = true)
    (exprs : List Expression.Expr) (mask : List Bool)
    (hexprs : List.Forall₂
      (fun e τ => e ∈ SPMF.support (genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] d τ))
      exprs (StrataGenerators.Stmt.substSig σ s.I).values)
    (hgen : exprs.all (binderAnnotsKnownIn C.knownTypes) = true) :
    (⟨StrataGenerators.Stmt.initChain
        ((StrataGenerators.Stmt.substSig σ s.M).filter (needsInit ctx) ++ T.filter (needsInit ctx))
        ++ [Statement.call s.pname (StrataGenerators.Stmt.mkArgs s.M T exprs mask) default],
      C, StrataGenerators.Stmt.insertAllCtx ctx
        ((StrataGenerators.Stmt.substSig σ s.M).filter (needsInit ctx)
          ++ T.filter (needsInit ctx))⟩ : GenStmtResult) ∈
      SPMF.support (genCallTail (G := SPMF) octx tvars immutableVars C ctx d pctx s σ T) := by
  unfold genCallTail
  rw [ite_eq_left ⟨hMusable, hNodup, hMnotFn⟩]
  simp only [mem_support_bind_iff]
  refine ⟨exprs, (mem_support_mapM_iff _ _ exprs).mpr hexprs, ?_⟩
  rw [ite_eq_left hgen]
  simp only [mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨mask, mem_support_argMask mask, rfl⟩

/-- A group that `genCallTail` emits extends the variable scope by its inline `init` chain, and
    that extension preserves functionality: the declared names are pairwise distinct (a sublist of
    the guard's `Nodup` key list) and each is fresh for `ctx` (that is what `needsInit` selected
    them for), so `insertAllCtx_functional` applies. -/
theorem genCallTail_outCtx {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat} {s : ProcSig}
    {σ : List (TyIdentifier × LMonoTy)} {T : @LMonoTySignature Unit}
    (hFun : Map.Functional ctx) (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallTail (G := SPMF) octx tvars immutableVars C ctx d pctx s σ T)) :
    Map.Functional r.outCtx := by
  obtain ⟨⟨_, hNodup, _⟩, exprs, mask, _, _, rfl⟩ := genCallTail_support hr
  show Map.Functional (insertAllCtx ctx _)
  rw [filter_needsInit_append]
  refine insertAllCtx_functional _ ctx hFun ?_ ?_
  · -- keys of a `filter` of a `Nodup`-keyed list are `Nodup`
    refine List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) ?_
    exact (congrArg List.Nodup (ListMap.keys_eq_map_fst _)).mp hNodup
  · -- every selected name passed `needsInit`, i.e. is absent from `ctx`
    intro p hp
    simpa [needsInit, VarCtx.isFresh, VarCtx.find?, Option.isNone_iff_eq_none] using
      (List.mem_filter.mp hp).2

/-- Every `genCallStmt` result extends the variable scope by its (inline) `init`
    chain, and that extension preserves functionality: the declared names are
    pairwise distinct (a sublist of the guard's `Nodup` key list) and each is fresh
    for `ctx` (that is what `needsInit` selected them for), so
    `insertAllCtx_functional` applies. The empty-`procs`/guard-false branches are
    the empty generator, so there is nothing to prove. -/
theorem genCallStmt_outCtx {procs : ProcSigCtx}
    {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat} (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx d pctx)) :
    Map.Functional r.outCtx := by
  cases procs with
  | nil => simp only [genCallStmt, mem_support_bot_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff] at hr
    obtain ⟨_, _, _, _, hr⟩ := hr
    exact genCallTail_outCtx hFun r hr

/-- A type that `sampleTyArg` draws from the generable types of the scope is well-kinded: it is a
    generable type, or the `bool` fallback, and both are well-kinded. -/
theorem sampleTyArg_wellKinded {procs : ProcSigCtx} {C : LContext CoreLParams}
    {ctx : VarCtx} (hWK : WellKindedOk octx procs C ctx) (t : LMonoTy)
    (ht : t ∈ SPMF.support (sampleTyArg (G := SPMF) (generableTypesFromCtx ctx.values [] octx))) :
    C.WellKindedTy t := by
  unfold sampleTyArg at ht
  split at ht
  · exact hWK.generable t (by rwa [mem_support_elements_iff] at ht)
  · rw [mem_support_pure_iff] at ht; rw [ht]; exact hWK.boolWK

/-- The instantiation that `genCallStmt` samples for the type parameters of a callee is
    well-kinded. -/
private theorem sampled_inst_wellKinded {procs : ProcSigCtx} {C : LContext CoreLParams}
    {ctx : VarCtx} (hWK : WellKindedOk octx procs C ctx) {typeArgs : List TyIdentifier}
    {σvals : List LMonoTy}
    (hσvals : σvals ∈ SPMF.support (typeArgs.mapM (fun _ =>
      sampleTyArg (G := SPMF) (generableTypesFromCtx ctx.values [] octx)))) :
    ∀ t ∈ (typeArgs.zip σvals).map Prod.snd, C.WellKindedTy t := by
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  obtain ⟨τ0, _, hmem⟩ :=
    forall₂_mem_left ((mem_support_mapM_iff _ typeArgs σvals).mp hσvals) q.2 (List.of_mem_zip hq).2
  exact sampleTyArg_wellKinded hWK q.2 hmem

/-- Each type of the in-out block of a callable procedure is well-kinded. -/
theorem sigsWK_inout {procs : ProcSigCtx} {C : LContext CoreLParams} {ctx : VarCtx}
    (hWK : WellKindedOk octx procs C ctx) {s : ProcSig} (hs : s ∈ procs) :
    ∀ t ∈ s.M.values, C.WellKindedTy t := by
  intro t ht
  refine hWK.sigsWK s hs t ?_
  rw [lm_values_append]
  exact List.mem_append_left _ ht

/-- Each type of the output-only block of a callable procedure is well-kinded. -/
theorem sigsWK_out {procs : ProcSigCtx} {C : LContext CoreLParams} {ctx : VarCtx}
    (hWK : WellKindedOk octx procs C ctx) {s : ProcSig} (hs : s ∈ procs) :
    ∀ t ∈ s.O.values, C.WellKindedTy t := by
  intro t ht
  refine hWK.sigsWK s hs t ?_
  rw [lm_values_append]
  exact List.mem_append_right _ ht

/-- The well-kindedness invariant after a `genCallTail` group. The inline `init` chain declares the
    callee's `σ`-instantiated in-out and out-only types, and those are well-kinded in `C` when the
    values of `σ` are, and when each out argument has the type of an instantiated out-only formal,
    because `substSig` preserves well-kindedness. Everything else in the output scope was already
    there. -/
theorem genCallTail_outCtx_wellKinded {procs : ProcSigCtx}
    {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat} {s : ProcSig}
    {σ : List (TyIdentifier × LMonoTy)} {T : @LMonoTySignature Unit}
    (hWK : WellKindedOk octx procs C ctx) (hs : s ∈ procs)
    (hσWK : ∀ t ∈ σ.map Prod.snd, C.WellKindedTy t)
    (hT : T.values = (StrataGenerators.Stmt.substSig σ s.O).values)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallTail (G := SPMF) octx tvars immutableVars C ctx d pctx s σ T)) :
    WellKindedOk octx procs r.outC r.outCtx := by
  -- A filtered signature block's values are among the block's values.
  have hfilt : ∀ (L : @LMonoTySignature Unit) (p : Identifier Unit × LMonoTy → Bool)
      (v : LMonoTy), v ∈ (L.filter p).map Prod.snd → v ∈ L.values := by
    intro L p v hv
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
    rw [ListMap.values_eq_map_snd]
    exact List.mem_map_of_mem (List.mem_filter.mp hq).1
  obtain ⟨_, exprs, mask, _, _, rfl⟩ := genCallTail_support hr
  show WellKindedOk octx procs C (insertAllCtx ctx _)
  refine { hWK with ctxWK := ?_ }
  intro ty hty
  rcases mem_values_insertAllCtx _ ctx hty with hnew | hold
  · rw [List.map_append] at hnew
    rcases List.mem_append.mp hnew with hM | hTm
    · exact substSig_values_wellKinded _ s.M hσWK
        (sigsWK_inout hWK hs) ty (hfilt _ _ ty hM)
    · refine substSig_values_wellKinded _ s.O hσWK
        (sigsWK_out hWK hs) ty ?_
      rw [← hT]
      exact hfilt _ _ ty hTm
  · exact hWK.ctxWK ty hold

/-- The `call` case of the well-kindedness invariant. The inline `init` chain declares
    the callee's `σ`-instantiated in-out and out-only types, and those are well-kinded in
    `C` because the sampled `σ` values are (`WellKindedOk.generable`, or the `bool`
    fallback) and `substSig` preserves well-kindedness. Everything else in the output scope
    was already there. -/
theorem genCallStmt_outCtx_wellKinded {procs : ProcSigCtx}
    {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat}
    (hWK : WellKindedOk octx procs C ctx)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx d pctx)) :
    WellKindedOk octx procs r.outC r.outCtx := by
  cases procs with
  | nil => simp only [genCallStmt, mem_support_bot_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff] at hr
    obtain ⟨s, hs, σvals, hσvals, hr⟩ := hr
    exact genCallTail_outCtx_wellKinded hWK ((mem_support_elements_iff (by simp)).mp hs)
      (sampled_inst_wellKinded hWK hσvals) (outTargets_values _ _ _ _) r hr

/-- The soundness of a `genCallTail` group. Each emitted *group* of a call (the `init`
    statements for each missing name, then the call, spliced inline) is a well-typed statement
    list from the scopes of `env.toTCtx ctx` to those of the extended scope, at every set of
    enclosing labels, when the callee `s` resolves in `P`, the sampled values of `σ` are well
    kinded in `C`, the operators, callee and scope types are well kinded in `C`, the operators and
    schemes agree with `C`, and the scope is functional. The out arguments `T` need the types of
    the instantiated out-only formals, by position, and each of them must be usable: the scope
    holds it at its type, or it is absent. -/
theorem genCallTail_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (procs : ProcSigCtx) (hProcs : ProcSigCorresponds procs P)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat)
    (hWK : WellKindedOk octx procs C ctx)
    (hops : ExprCtxOk C [] [] octx pctx) (hFun : Map.Functional ctx)
    (s : ProcSig) (hs : s ∈ procs) (σ : List (TyIdentifier × LMonoTy)) (T : @LMonoTySignature Unit)
    (hσWK : ∀ t ∈ σ.map Prod.snd, C.WellKindedTy t)
    (hTVals : T.values = (StrataGenerators.Stmt.substSig σ s.O).values)
    (hTusable : T.all (usableName immutableVars ctx) = true)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallTail (G := SPMF) octx tvars immutableVars C ctx d pctx s σ T)) :
    StatementsWellTyped P C (env.toTCtx ctx).types labels r.stmts r.outC
      (env.toTCtx r.outCtx).types := by
  obtain ⟨⟨hMusable, hNodup, _⟩, exprs, mask, hF₂, hgenAll, rfl⟩ := genCallTail_support hr
  -- Name the instantiated signature blocks.
  generalize hMσ : StrataGenerators.Stmt.substSig σ s.M = Mσ at hMusable hNodup ⊢
  generalize hIσ : StrataGenerators.Stmt.substSig σ s.I = Iσ at hF₂
  generalize hOσ : StrataGenerators.Stmt.substSig σ s.O = Oσ at hTVals
  have hallusable : (List.append Mσ T).all (usableName immutableVars ctx) = true := by
    rw [List.all_eq_true]
    intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact List.all_eq_true.mp hMusable q h
    · exact List.all_eq_true.mp hTusable q h
  -- Callee signature facts from the correspondence.
  obtain ⟨proc, hfind, _, hInputs, hOutputs, hIdisjOut, hOutNodup⟩ := hProcs s hs
  have hMnotO : ∀ k ∈ s.M.keys, k ∉ s.O.keys := by
    rw [lm_keys_append] at hOutNodup
    exact fun k hk hkO => (List.nodup_append.mp hOutNodup).2.2 k hk k hkO rfl
  have hExLen : exprs.length = s.I.length := by
    rw [hF₂.length_eq, ← hIσ, lm_values_length, StrataGenerators.Stmt.substSig_length]
  -- Each input is well-typed at the instantiated input type `subst [σ] (s.I.values[i])`.
  have hExTy : ∀ i (hi : i < exprs.length) (hj : i < s.I.values.length),
      ExprWellTyped C (env.toTCtx ctx).types (exprs[i]'hi)
        (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (s.I.values[i]'hj)) := by
    intro i hi hj
    have hjσ : i < Iσ.values.length := by
      rw [← hIσ, lm_values_length, StrataGenerators.Stmt.substSig_length, ← lm_values_length]
      exact hj
    have hmem : exprs[i]'hi ∈ SPMF.support
        (genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] d (Iσ.values[i]'hjσ)) := by
      simpa only [List.get_eq_getElem] using hF₂.get hi hjσ
    -- `Iσ.values[i] = subst [σ] (s.I.values[i])` (as a value equation, so the
    -- index proof `hjσ` is untouched).
    have hval : Iσ.values[i]'hjσ =
        LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (s.I.values[i]'hj) := by
      have hjσ' : i < (StrataGenerators.Stmt.substSig σ s.I).values.length := by
        rw [hIσ]; exact hjσ
      rw [← StrataGenerators.Stmt.substSig_values_getElem σ s.I i hjσ' hj]
      congr 1; rw [hIσ]
    rw [← hval]
    exact genLExpr_exprWellTyped_of_known hops (env.corr ctx) hFun hmem
      (List.all_eq_true.mp hgenAll _ (List.getElem_mem hi))
  -- Each required name (in the instantiated write-list `Mσ ++ T`) is *either* already bound
  -- at its recorded type, so the call reuses it, *or* absent, so the call declares it. That
  -- is the `usable` guard of the generator, moved across `VarCtxCorresponds`.
  have hReuse : ∀ p ∈ (Mσ ++ T).toList,
      (env.toTCtx ctx).types.find? p.1 = some (.forAll [] p.2) ∨
      (env.toTCtx ctx).types.find? p.1 = none := by
    intro q hq
    have hq' := List.all_eq_true.mp hallusable q hq
    rcases hfind_q : ctx.find? q.1 with _ | τ
    · exact Or.inr ((env.corr ctx).2 q.1 (by simp [VarCtx.isFresh, hfind_q]))
    · have hnotinit : needsInit ctx q = false := by
        simp [needsInit, VarCtx.isFresh, hfind_q]
      have hreuse : reusable immutableVars ctx q = true := by
        simp only [usableName, hnotinit, Bool.or_false] at hq'; exact hq'
      have hτ : τ = q.2 := by
        simp only [reusable, hfind_q, Bool.and_eq_true, beq_iff_eq, Option.some.injEq]
          at hreuse
        exact hreuse.1
      have hb := (env.corr ctx).1 q.1 τ hfind_q
      rw [hτ] at hb
      exact Or.inl hb
  -- Every type the init chain stores is well-kinded in `C`.
  have hwk : ∀ p ∈ (StrataGenerators.Stmt.substSig σ s.M ++ T).toList,
      C.WellKindedTy p.2 := by
    intro q hq
    rcases List.mem_append.mp hq with hqM | hqT
    · exact substSig_values_wellKinded σ s.M hσWK
        (sigsWK_inout hWK hs) q.2 (by rw [ListMap.values_eq_map_snd]; exact List.mem_map_of_mem hqM)
    · have hqv : q.2 ∈ T.values := by
        rw [ListMap.values_eq_map_snd]; exact List.mem_map_of_mem hqT
      rw [hTVals, ← hOσ] at hqv
      exact substSig_values_wellKinded σ s.O hσWK
        (sigsWK_out hWK hs) q.2 hqv
  -- Move both the emitted chain and the output scope to the single `missingIn`
  -- filter over the scopes of `env.toTCtx ctx` that `call_mixed_body_sound` speaks about.
  show StatementsWellTyped P C (env.toTCtx ctx).types labels
    (initChain (Mσ.filter (needsInit ctx) ++ T.filter (needsInit ctx)) ++ _) C
    (env.toTCtx
      (insertAllCtx ctx (Mσ.filter (needsInit ctx) ++ T.filter (needsInit ctx)))).types
  refine StatementsWellTyped_out_equiv ?_
    (env.toTCtx_insertAllCtx (Mσ.filter (needsInit ctx) ++ T.filter (needsInit ctx)) ctx)
  rw [filter_needsInit_append, filter_needsInit_eq_missingIn env ctx]
  -- `call_mixed_body_sound` takes declared blocks + `σ`; `Mσ`/`Oσ` are the
  -- instantiated ones the generator used. Rewrite them back to `substSig σ …`.
  rw [← hMσ] at hNodup hReuse ⊢
  rw [← hOσ] at hTVals
  exact call_mixed_body_sound σ s.M s.I s.O T exprs mask hfind hInputs hOutputs
    hExLen hTVals hExTy hIdisjOut hMnotO hNodup hReuse hwk

/-- The soundness of `genCallStmt`, at each depth. Each emitted *group* of a call (the `init`
    statements for each missing name, then the call, spliced inline) is a well-typed statement
    list from the scopes of `env.toTCtx ctx` to those of the extended scope, at every set of
    enclosing labels, when every callable procedure resolves in `P`, the operator, callee and
    scope types are well kinded in `C`, the operators and schemes agree with `C`, and the scope
    is functional. -/
theorem genCallStmt_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (procs : ProcSigCtx) (hProcs : ProcSigCorresponds procs P)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat)
    -- The inline `init` chain a call emits stores the callee's σ-instantiated written-to
    -- types, and the `init` rule requires the stored monotype to be well-kinded in `C`.
    -- `WellKindedOk` is exactly what that needs.
    (hWK : WellKindedOk octx procs C ctx)
    (hops : ExprCtxOk C [] [] octx pctx) (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx d pctx)) :
    StatementsWellTyped P C (env.toTCtx ctx).types labels r.stmts r.outC
      (env.toTCtx r.outCtx).types := by
  cases procs with
  | nil => simp only [genCallStmt, mem_support_bot_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff] at hr
    obtain ⟨s, hs, σvals, hσvals, hr⟩ := hr
    exact genCallTail_sound P env _ hProcs C ctx d hWK hops hFun s
      ((mem_support_elements_iff (by simp)).mp hs) _ _ (sampled_inst_wellKinded hWK hσvals)
      (outTargets_values _ _ _ _) (outTargets_all_usableName _ _ _ _) r hr

-- ── Procedure-call completeness (forward membership) ──────────────────────

/-- **Forward membership for `genCallStmt` (Part 2 of call completeness).** Given a
    callee `s` in the procedure context, whose in-out block is usable, whose
    combined write-key list is `Nodup`, and whose in-out names that have to be declared are not
    function names (the generator's own guard), and by-value inputs `exprs` each reachable by
    `genLExpr` at the declared input type, whose binder annotations the generator can make, the
    output of the recipe of the generator, which is the chain of the `init` statements for each missing name
    followed by the assembled call, is in the support of `genCallStmt`.

    This is the completeness analogue of `genCallStmt_sound`: it runs the
    `genCallStmt` `do`-block *forward* (`elements` membership of `s`, the
    type-instantiation sampling, the guard branch, `mapM` membership of `exprs`,
    `pure`), rather than inverting it. The chosen instantiation is `σ := s.typeArgs.zip σvals`
    for a sampled `σvals` (`hσvals` places it in the sampling step's support), and
    the emitted group/output scope are stated over the instantiated blocks
    `substSig σ s.M` / `substSig σ s.O`, with `T := outTargets immutableVars ctx (substSig σ s.O)`.
    A monomorphic callee (`s.typeArgs = []`) forces `σvals = []`, `σ = []`, and
    `substSig [] = id`, recovering the previous statement.

    `mask` is the argument-order mask the generator samples (see `mkArgs`). Every
    `List Bool` is reachable, so the caller may pick any interleaving of the
    by-value inputs and the out targets. -/
theorem genCallStmt_mem_complete (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat)
    (s : ProcSig) (hs : s ∈ procs)
    (σvals : List LMonoTy)
    (hσvals : σvals ∈ SPMF.support
      (s.typeArgs.mapM (fun _ =>
        if hg : (generableTypesFromCtx ctx.values [] octx).length > 0 then
          elements (generableTypesFromCtx ctx.values [] octx)
            (by apply List.ne_nil_of_length_pos; assumption)
        else pure (.bool : LMonoTy)) : SPMF (List LMonoTy)))
    (exprs : List Expression.Expr) (mask : List Bool)
    (hMusable : (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).all
      (usableName immutableVars ctx) = true)
    (hNodup : (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M
      ++ outTargets immutableVars ctx (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O)
        (functionNames C)).keys.Nodup)
    (hMnotFn : ((StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).filter
      (needsInit ctx)).all (fun q => !(functionNames C).contains q.1.name) = true)
    (hexprs : List.Forall₂
      (fun e τ => e ∈ SPMF.support (genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] d τ))
      exprs (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.I).values)
    (hgen : exprs.all (binderAnnotsKnownIn C.knownTypes) = true) :
    (⟨StrataGenerators.Stmt.initChain
        ((StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).filter (needsInit ctx)
          ++ (outTargets immutableVars ctx
                (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O) (functionNames C)).filter (needsInit ctx))
        ++ [Statement.call s.pname
              (StrataGenerators.Stmt.mkArgs s.M
                (outTargets immutableVars ctx
                  (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O) (functionNames C)) exprs mask) default],
      C, StrataGenerators.Stmt.insertAllCtx ctx
        ((StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M).filter (needsInit ctx)
          ++ (outTargets immutableVars ctx
                (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O) (functionNames C)).filter (needsInit ctx))⟩
      : GenStmtResult) ∈
      SPMF.support (genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx d pctx) := by
  -- `procs` is non-empty (it contains `s`), so the `p₀ :: ps` branch fires.
  cases procs with
  | nil => exact absurd hs (by simp)
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff]
    refine ⟨s, (mem_support_elements_iff (by simp)).mpr hs, σvals, hσvals, ?_⟩
    exact genCallTail_mem hMusable hNodup hMnotFn exprs mask hexprs hgen

-- ── Guard / measure / invariant soundness helpers ────────────────────────

/-- Any `.det`-guard produced by `genCondOrNondet` (at depth `d`) carries a well-typed boolean
    expression, when the operators and schemes agree with `C`,
    the scope is functional and its types are well kinded in `C`. -/
theorem genCondOrNondet_det_sound (env : GenStmtSoundEnv octx tvars pctx) (d : Nat) (ctx : VarCtx)
    (cond : ExprOrNondet Expression)
    {C : LContext CoreLParams} (hops : ExprCtxOk C [] [] octx pctx) (hFun : Map.Functional ctx)
    (hwk : ∀ ty ∈ ctx.values, C.WellKindedTy ty)
    (hc : cond ∈ SPMF.support (genCondOrNondet (G := SPMF) octx tvars ctx d pctx))
    (g : Expression.Expr) (hg : cond = .det g) :
    ExprWellTyped C (env.toTCtx ctx).types g .bool := by
  revert cond; show IsSoundFor _ _; rw [IsSoundFor.iff_obs, genCondOrNondet]
  walk [(isSoundFor_self_support (genLExpr _ _ _ _ _ _ _)).obs]
  all_goals cases ‹_ = ExprOrNondet.det g›
  exact env.exprWellTyped hops hFun hwk (knownInstance_bool hops.arities) ‹_›

/-- Any `some`-measure produced by `genOptMeasure` (at depth `d`) carries a well-typed integer
    expression, when the operators and schemes agree with `C`,
    the scope is functional and its types are well kinded in `C`. -/
theorem genOptMeasure_some_sound (env : GenStmtSoundEnv octx tvars pctx) (d : Nat) (ctx : VarCtx)
    (m? : Option Expression.Expr) {C : LContext CoreLParams}
    (hops : ExprCtxOk C [] [] octx pctx) (hFun : Map.Functional ctx)
    (hwk : ∀ ty ∈ ctx.values, C.WellKindedTy ty)
    (hm : m? ∈ SPMF.support (genOptMeasure (G := SPMF) octx tvars ctx d pctx))
    (m : Expression.Expr) (hmeq : m? = some m) :
    ExprWellTyped C (env.toTCtx ctx).types m .int := by
  simp only [genOptMeasure,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)] at hm
  rcases hm with hm | ⟨e, he, hm⟩
  · subst hm
    simp at hmeq
  · subst hm
    obtain rfl := Option.some.inj hmeq
    exact env.exprWellTyped hops hFun hwk (knownInstance_int hops.arities) he

/-- Every invariant produced by `genInvariants` (of length at most `m`, at depth `d`) carries a well-typed boolean
    expression, when the operators and schemes agree with `C`,
    the scope is functional and its types are well kinded in `C`. -/
theorem genInvariants_sound (env : GenStmtSoundEnv octx tvars pctx) (m d : Nat) (ctx : VarCtx)
    (invs : List (String × Expression.Expr)) {C : LContext CoreLParams}
    (hops : ExprCtxOk C [] [] octx pctx) (hFun : Map.Functional ctx)
    (hwk : ∀ ty ∈ ctx.values, C.WellKindedTy ty)
    (hinv : invs ∈ SPMF.support (genInvariants (G := SPMF) octx tvars ctx m d pctx))
    (p : String × Expression.Expr) (hp : p ∈ invs) :
    ExprWellTyped C (env.toTCtx ctx).types p.2 .bool := by
  simp only [genInvariants, mem_support_listOfMaxLength_iff] at hinv
  have hp_supp := hinv.2 p hp
  simp only [genInvariant, mem_support_bind_iff, mem_support_pure_iff] at hp_supp
  obtain ⟨l, _, e, he, rfl⟩ := hp_supp
  exact env.exprWellTyped hops hFun hwk (knownInstance_bool hops.arities) he

-- ── Facts about the targets and the instantiation of the matching call ────────────────────────

/-- The targets that `pickOutTargets` draws: one per formal, and each chosen variable is a
    candidate. -/
theorem pickOutTargets_spec :
    ∀ (formals cands : List (Identifier Unit × LMonoTy))
      (chosen : List (Option (Identifier Unit × LMonoTy))),
      chosen ∈ SPMF.support (pickOutTargets (G := SPMF) cands formals) →
      chosen.length = formals.length ∧ ∀ v, some v ∈ chosen → v ∈ cands := by
  intro formals
  induction formals with
  | nil =>
    intro cands chosen h
    simp only [pickOutTargets, mem_support_pure_iff] at h
    subst h
    simp
  | cons q rest ih =>
    intro cands chosen h
    simp only [pickOutTargets, mem_support_bind_iff, mem_support_pure_iff] at h
    obtain ⟨c, hc, more, hmore, rfl⟩ := h
    have hcmem := (mem_support_elements_iff (by simp)).mp hc
    cases c with
    | none =>
      obtain ⟨hlen, hall⟩ := ih cands more hmore
      refine ⟨by simp [hlen], ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · cases hv
      · exact hall v hv
    | some w =>
      obtain ⟨hlen, hall⟩ := ih (cands.filter (fun q => !(q.1 == w.1))) more hmore
      refine ⟨by simp [hlen], ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · cases hv
        simpa using hcmem
      · exact List.mem_of_mem_filter (hall v hv)

/-- The out arguments that `matchOutTargets` returns have the types of the instantiated out-only
    formals, in order, when there is a choice for each formal. -/
theorem matchOutTargets_values (base : Nat) (Oσ : @LMonoTySignature Unit)
    (chosen : List (Option (Identifier Unit × LMonoTy))) (hlen : Oσ.length ≤ chosen.length) :
    (matchOutTargets base Oσ chosen).values = Oσ.values := by
  unfold matchOutTargets
  refine (listMap_values_map _ _).trans ?_
  rw [ListMap.values_eq_map_snd (m := Oσ)]
  refine (List.map_congr_left (g := fun (x : ((Identifier Unit × LMonoTy) ×
      Option (Identifier Unit × LMonoTy)) × Nat) => x.1.1.2) ?_).trans ?_
  · rintro ⟨⟨q, c⟩, i⟩ _
    cases c <;> rfl
  rw [show (fun (x : ((Identifier Unit × LMonoTy) × Option (Identifier Unit × LMonoTy)) × Nat) =>
      x.1.1.2)
      = (fun p : (Identifier Unit × LMonoTy) × Option (Identifier Unit × LMonoTy) => p.1.2)
        ∘ Prod.fst
      from rfl, ← List.map_map, List.zipIdx_map_fst,
    show (fun p : (Identifier Unit × LMonoTy) × Option (Identifier Unit × LMonoTy) => p.1.2)
      = Prod.snd ∘ Prod.fst from rfl, ← List.map_map, List.map_fst_zip hlen]

/-- Each out argument of `matchOutTargets` either takes the name of a chosen variable, with the
    type of the formal, or has an invented name. -/
theorem matchOutTargets_mem (base : Nat) (Oσ : @LMonoTySignature Unit)
    (chosen : List (Option (Identifier Unit × LMonoTy))) (q : Identifier Unit × LMonoTy)
    (hq : q ∈ (matchOutTargets base Oσ chosen).toList) :
    (∃ (qf v : Identifier Unit × LMonoTy), (qf, some v) ∈ Oσ.toList.zip chosen ∧ q = (v.1, qf.2)) ∨
    (∃ (qf : Identifier Unit × LMonoTy) (i : Nat), q = freshOut base i qf.2) := by
  unfold matchOutTargets at hq
  obtain ⟨⟨⟨qf, c⟩, i⟩, hmem, rfl⟩ := List.mem_map.mp hq
  have hz : (qf, c) ∈ Oσ.zip chosen := List.fst_mem_of_mem_zipIdx hmem
  cases c with
  | none => exact Or.inr ⟨qf, i, rfl⟩
  | some v => exact Or.inl ⟨qf, v, hz, rfl⟩

/-- Each out argument of `matchOutTargets` is usable: a chosen variable has the type of its formal
    and is mutable, so it can be reused, and an invented name is absent from the scope. -/
theorem matchOutTargets_all_usableName (ctx : VarCtx) (hFun : Map.Functional ctx) (base : Nat)
    (hbase : maxNameLen ctx ≤ base) (Oσ : @LMonoTySignature Unit)
    (chosen : List (Option (Identifier Unit × LMonoTy)))
    (hmatched : targetsMatched Oσ chosen = true)
    (hcand : ∀ v, some v ∈ chosen → List.Mem v ctx ∧ immutableVars.contains v.1 = false) :
    (matchOutTargets base Oσ chosen).all (usableName immutableVars ctx) = true := by
  refine List.all_eq_true.mpr fun q hq => ?_
  rcases matchOutTargets_mem base Oσ chosen q hq with ⟨qf, v, hz, rfl⟩ | ⟨qf, i, rfl⟩
  · have htm : (qf.2 == v.2) = true := by
      unfold targetsMatched at hmatched
      simpa using List.all_eq_true.mp hmatched (qf, some v) hz
    have hty : qf.2 = v.2 := beq_iff_eq.mp htm
    obtain ⟨hvmem, himm⟩ := hcand v (List.of_mem_zip hz).2
    have hfind : ctx.find? v.1 = some v.2 :=
      Map.find?_of_mem_of_functional ctx v.1 v.2 hFun hvmem
    simp only [usableName, reusable, hfind, hty, himm, beq_self_eq_true, Bool.not_false,
      Bool.and_self, Bool.true_or]
  · simp [usableName, needsInit, freshOut, indexedFreshName_isFresh_of_le ctx hbase i]

/-- An out argument of `matchOutTargets` that the scope binds is not immutable. -/
theorem matchOutTargets_not_immutable (ctx : VarCtx) (base : Nat)
    (hbase : maxNameLen ctx ≤ base) (Oσ : @LMonoTySignature Unit)
    (chosen : List (Option (Identifier Unit × LMonoTy)))
    (hcand : ∀ v, some v ∈ chosen → immutableVars.contains v.1 = false) :
    ∀ q ∈ (matchOutTargets base Oσ chosen).toList, ctx.find? q.1 ≠ none →
      immutableVars.contains q.1 = false := by
  intro q hq hne
  rcases matchOutTargets_mem base Oσ chosen q hq with ⟨qf, v, hz, rfl⟩ | ⟨qf, i, rfl⟩
  · exact hcand v (List.of_mem_zip hz).2
  · have hfresh := indexedFreshName_isFresh_of_le ctx hbase i
    simp only [VarCtx.isFresh, Option.isNone_iff_eq_none] at hfresh
    exact absurd hfresh hne

/-- A usable name that the scope binds is not immutable. -/
theorem usableName_not_immutable {ctx : VarCtx} {q : Identifier Unit × LMonoTy}
    (h : usableName immutableVars ctx q = true) (hne : ctx.find? q.1 ≠ none) :
    immutableVars.contains q.1 = false := by
  simp only [usableName, reusable, needsInit, VarCtx.isFresh, Bool.or_eq_true, Bool.and_eq_true,
    Option.isNone_iff_eq_none, beq_iff_eq, Bool.not_eq_true'] at h
  rcases h with ⟨_, h⟩ | h
  · exact h
  · exact absurd h hne

/-- Each result of a successful `mapM` in `Option` comes from one of the inputs. -/
theorem option_mapM_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → ∀ y ∈ r, ∃ x ∈ l, f x = some y := by
  intro l
  induction l with
  | nil =>
    intro r h y hy
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact absurd hy List.not_mem_nil
  | cons a rest ih =>
    intro r h y hy
    rcases hfa : f a with _ | b
    · simp [List.mapM_cons, hfa] at h
    rcases hrest : List.mapM f rest with _ | rs
    · simp [List.mapM_cons, hfa, hrest] at h
    simp only [List.mapM_cons, hfa, hrest] at h
    have h' : some (b :: rs) = some r := h
    have hr : b :: rs = r := Option.some.inj h'
    subst hr
    have hb : f a = some b := hfa
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, hb⟩
    · obtain ⟨x, hx, hfx⟩ := ih rs hrest y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- Each unifier that `matchTargets` returns keeps its range registered in the known types, when
    the formal types and the types of the chosen variables are registered. -/
theorem matchTargets_rangeKnown (ks : KnownTypes) (formals : @LMonoTySignature Unit)
    (chosen : List (Option (Identifier Unit × LMonoTy))) (substs : List Lambda.Subst)
    (h : matchTargets formals chosen = some substs)
    (hf : ∀ ty ∈ formals.values, LMonoTy.knownInstance ty ks = true)
    (hc : ∀ v, some v ∈ chosen → LMonoTy.knownInstance v.2 ks = true) :
    ∀ sb ∈ substs, Subst.RangeKnown sb ks := by
  intro sb hsb
  obtain ⟨⟨q, c⟩, hqc, hfx⟩ := option_mapM_mem _ _ substs h sb hsb
  have hz := List.of_mem_zip hqc
  cases c with
  | none =>
    simp only [Option.some.injEq] at hfx
    subst hfx
    intro mty hmty
    exact absurd hmty (by simp [Strata.Util.HMaps.values])
  | some v =>
    obtain ⟨sa, hua, hguard⟩ := Option.bind_eq_some_iff.mp hfx
    split at hguard
    · simp only [Option.some.injEq] at hguard
      subst hguard
      simp only [unifyTypes] at hua
      split at hua
      · rename_i si hsi
        simp only [Option.some.injEq] at hua
        subst hua
        have hqk : LMonoTy.knownInstance q.2 ks = true := by
          refine hf q.2 ?_
          rw [ListMap.values_eq_map_snd]
          exact List.mem_map_of_mem hz.1
        have hempty : Subst.RangeKnown SubstInfo.empty.subst ks := by
          intro mty hmty
          simp only [SubstInfo.empty, Subst.empty, Strata.Util.HMaps.values] at hmty
          exact absurd hmty List.not_mem_nil
        have hcs : Constraints.Known [(q.2, v.2)] ks := by
          intro c hc'
          rw [List.mem_singleton.mp hc']
          exact ⟨hqk, hc v hz.2⟩
        exact Constraints.unify_RangeKnown ks _ _ si hsi hempty hcs
      · simp at hua
    · simp at hguard

/-- The type that `matchedTyArg` draws for a type parameter is well-kinded when the unifiers keep
    their range registered, and the types of the scope are well-kinded. -/
theorem matchedTyArg_wellKinded {procs : ProcSigCtx} {C : LContext CoreLParams} {ctx : VarCtx}
    (hWK : WellKindedOk octx procs C ctx) (substs : List Lambda.Subst)
    (hsub : ∀ sb ∈ substs, Subst.RangeKnown sb C.knownTypes) (f : TyIdentifier) (t : LMonoTy)
    (ht : t ∈ SPMF.support
      (matchedTyArg (G := SPMF) (generableTypesFromCtx ctx.values [] octx) substs f)) :
    C.WellKindedTy t := by
  unfold matchedTyArg at ht
  rcases hfs : substs.findSome? (fun sb => Strata.Util.HMaps.find? sb f) with _ | t'
  · rw [hfs] at ht
    exact sampleTyArg_wellKinded hWK t ht
  · rw [hfs] at ht
    simp only [mem_support_pure_iff] at ht
    subst ht
    obtain ⟨sb, hsbmem, hsbfind⟩ := List.exists_of_findSome?_eq_some hfs
    exact LMonoTy.knownInstance_wellKinded t C.knownTypes
      (hsub sb hsbmem t (Strata.Util.HMaps.find?_mem_values sb hsbfind))

/-- **What a `genCallStmtMatch` result looks like.** The result is a `genCallTail` group for a
    callee `s` of the procedure context, the instantiation `s.typeArgs.zip σvals`, and the out
    arguments that `matchOutTargets` builds from the chosen targets. There is a chosen target for
    each out-only formal. Each chosen variable is in the scope and is mutable, and each instantiated
    formal has the type of its chosen variable. When the scope, the callees and the operators are
    well-kinded, each instantiated type argument is well-kinded. -/
theorem genCallStmtMatch_cases {procs : ProcSigCtx} {C : LContext CoreLParams} {ctx : VarCtx}
    {d : Nat} (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmtMatch (G := SPMF) octx tvars immutableVars procs C ctx d pctx)) :
    ∃ (s : ProcSig) (chosen : List (Option (Identifier Unit × LMonoTy))) (σvals : List LMonoTy),
      s ∈ procs ∧
      (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O).length ≤ chosen.length ∧
      (∀ v, some v ∈ chosen → List.Mem v ctx ∧ immutableVars.contains v.1 = false) ∧
      (WellKindedOk octx procs C ctx →
        ∀ t ∈ (s.typeArgs.zip σvals).map Prod.snd, C.WellKindedTy t) ∧
      targetsMatched (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O) chosen = true ∧
      r ∈ SPMF.support (genCallTail (G := SPMF) octx tvars immutableVars C ctx d pctx s
        (s.typeArgs.zip σvals)
        (matchOutTargets (outNameBase ctx (functionNames C))
          (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O) chosen)) := by
  cases procs with
  | nil => simp only [genCallStmtMatch, mem_support_bot_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmtMatch, mem_support_bind_iff] at hr
    obtain ⟨s, hs, chosen, hchosen, hr⟩ := hr
    have hs' := (mem_support_elements_iff (by simp)).mp hs
    obtain ⟨hlen, hpick⟩ := pickOutTargets_spec _ _ chosen hchosen
    have hcand : ∀ v, some v ∈ chosen → List.Mem v ctx ∧ immutableVars.contains v.1 = false := by
      intro v hv
      have hvc := List.mem_filter.mp (hpick v hv)
      refine ⟨hvc.1, ?_⟩
      simpa using (Bool.and_eq_true _ _ |>.mp hvc.2).1
    split at hr
    · simp only [mem_support_bot_iff] at hr
    · rename_i substs hmatch
      simp only [mem_support_bind_iff] at hr
      obtain ⟨σvals, hσvals, hr⟩ := hr
      split at hr
      · rename_i hmatched
        have hσWK : WellKindedOk octx (p₀ :: ps) C ctx →
            ∀ t ∈ (s.typeArgs.zip σvals).map Prod.snd, C.WellKindedTy t := by
          intro hWK
          -- Each formal of the renamed out block and each chosen variable has a registered type.
          have hρ : ∀ t ∈ (matchRenaming octx tvars ctx s).map Prod.snd, C.WellKindedTy t := by
            intro t ht
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
            obtain ⟨x, _, hx⟩ := List.mem_map.mp (List.of_mem_zip hq).2
            rw [← hx]
            intro ref n hmem
            simp [getTypeConsArities] at hmem
          have hf : ∀ ty ∈ (StrataGenerators.Stmt.substSig (matchRenaming octx tvars ctx s)
                s.O).values, LMonoTy.knownInstance ty C.knownTypes = true := by
            intro ty hty
            refine LMonoTy.wellKinded_knownInstance _ _ ?_
            exact substSig_values_wellKinded _ s.O hρ
              (sigsWK_out hWK hs') ty hty
          have hc : ∀ v, some v ∈ chosen → LMonoTy.knownInstance v.2 C.knownTypes = true := by
            intro v hv
            refine LMonoTy.wellKinded_knownInstance _ _ (hWK.ctxWK v.2 ?_)
            rw [Map.values_eq_map_snd]
            exact List.mem_map_of_mem (hcand v hv).1
          have hsub := matchTargets_rangeKnown C.knownTypes _ chosen substs hmatch hf hc
          intro t ht
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
          obtain ⟨f, _, hmem⟩ :=
            forall₂_mem_left ((mem_support_mapM_iff _ _ σvals).mp hσvals) q.2 (List.of_mem_zip hq).2
          exact matchedTyArg_wellKinded hWK substs hsub f q.2 hmem
        have hlen' : (StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.O).length
            ≤ chosen.length := by
          rw [StrataGenerators.Stmt.substSig_length]; omega
        exact ⟨s, chosen, σvals, hs', hlen', hcand, hσWK, hmatched, hr⟩
      · simp only [mem_support_bot_iff] at hr

-- ── The matching call generator `genCallStmtMatch`: facts that `genStmt` needs ──────────────────

/-- Every `genCallStmtMatch` result extends the variable scope by its inline `init` chain, and that
    extension keeps the scope functional: it binds each name at most once. -/
theorem genCallStmtMatch_outCtx {procs : ProcSigCtx}
    {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat} (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmtMatch (G := SPMF) octx tvars immutableVars procs C ctx d pctx)) :
    Map.Functional r.outCtx := by
  obtain ⟨_, _, _, _, _, _, _, _, hr⟩ := genCallStmtMatch_cases r hr
  exact genCallTail_outCtx hFun r hr

/-- Every `genCallStmtMatch` result extends the variable scope only by well-kinded types: when the
    scope, the callees and the operators are well-kinded, so are the extended scope and the
    ambient context of the result. -/
theorem genCallStmtMatch_outCtx_wellKinded {procs : ProcSigCtx}
    {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat}
    (hWK : WellKindedOk octx procs C ctx)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmtMatch (G := SPMF) octx tvars immutableVars procs C ctx d pctx)) :
    WellKindedOk octx procs r.outC r.outCtx := by
  obtain ⟨_, _, _, hs, hlen, _, hσWK, _, hr⟩ := genCallStmtMatch_cases r hr
  exact genCallTail_outCtx_wellKinded hWK hs (hσWK hWK) (matchOutTargets_values _ _ _ hlen) r hr

/-- A `genCallStmtMatch` result leaves the ambient context `C` unchanged. -/
theorem genCallStmtMatch_outC {procs : ProcSigCtx}
    {C : LContext CoreLParams} {ctx : VarCtx} {d : Nat}
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmtMatch (G := SPMF) octx tvars immutableVars procs C ctx d pctx)) :
    r.outC = C := by
  obtain ⟨_, _, _, _, _, _, _, _, hr⟩ := genCallStmtMatch_cases r hr
  obtain ⟨_, exprs, mask, _, _, rfl⟩ := genCallTail_support hr
  rfl

/-- Soundness of `genCallStmtMatch`: each emitted group (the `init` statements for each missing
    name, then the call, spliced inline) is a well-typed statement list from the scopes of
    `env.toTCtx ctx` to those of the extended scope, at every set of enclosing labels, when every
    callable procedure resolves in `P`, the operator, callee and scope types are well kinded in
    `C`, the operators and schemes agree with `C`, and the scope is functional. -/
theorem genCallStmtMatch_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (procs : ProcSigCtx) (hProcs : ProcSigCorresponds procs P)
    (C : LContext CoreLParams) (ctx : VarCtx) (d : Nat)
    (hWK : WellKindedOk octx procs C ctx)
    (hops : ExprCtxOk C [] [] octx pctx) (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmtMatch (G := SPMF) octx tvars immutableVars procs C ctx d pctx)) :
    StatementsWellTyped P C (env.toTCtx ctx).types labels r.stmts r.outC
      (env.toTCtx r.outCtx).types := by
  obtain ⟨s, chosen, _, hs, hlen, hcand, hσWK, hmatched, hr⟩ := genCallStmtMatch_cases r hr
  exact genCallTail_sound P env procs hProcs C ctx d hWK hops hFun s hs _ _ (hσWK hWK)
    (matchOutTargets_values _ _ _ hlen)
    (matchOutTargets_all_usableName ctx hFun _ (maxNameLen_le_outNameBase ctx _) _ chosen
      hmatched hcand) r hr

-- ── Mutual soundness of genStmt / genStmtChain ───────────────────────────────

/-- Unfolds one step of `genStmt` and its leaf generators, and walks a soundness goal over them.
    One goal is left per branch, with the membership of each draw in context. The output scope of a
    nesting branch is the input one, so the bodies need no recursion. -/
local macro "walk_genStmt_leaves" : tactic => `(tactic| (
  rw [IsSoundFor.iff_obs]
  cases ‹Nat› <;> rw [genStmt] <;> unfold genCmdStmt genExitStmt genTypeDeclStmt <;>
    walk [(isSoundFor_self_support (genCmd _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genCallStmt _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genCallStmtMatch _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genTypeConstructor _)).obs,
      (isSoundFor_self_support (genFreshLabel _)).obs,
      (isSoundFor_self_support (genStmtChain _ _ _ _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genLExpr _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genCondOrNondet _ _ _ _ _)).obs,
      (isSoundFor_self_support (genOptMeasure _ _ _ _ _)).obs,
      (isSoundFor_self_support (genInvariants _ _ _ _ _ _)).obs]))

/-- `genStmt` keeps the context *functional*. Each nesting constructor, which is a `block`, an `ite` or a
    `loop`, has a lexical scope. Its output scope is the *input* context, and the code discards the scope that
    the body threads. Each leaf that is not a `cmd` also leaves the context unchanged. Therefore the only case
    that can grow
    the context is `cmd`, handled by `genCmd_outCtx_functional`. No recursion into
    the body is needed, so this stands outside the soundness `mutual` block. -/
theorem genStmt_outCtx_functional
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat) (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n maxStmtSeqLen)) :
    Map.Functional r.outCtx := by
  revert r; show IsSoundFor _ _; walk_genStmt_leaves
  all_goals first
    | exact hFun
    | exact genCmd_outCtx_functional octx pctx tvars immutableVars ctx _ hFun _ ‹_›
    | exact genCallStmt_outCtx hFun _ ‹_›
    | exact genCallStmtMatch_outCtx hFun _ ‹_›

/-- **`genStmt` keeps `WellKindedOk`.** The invariant is stated in `LContext.WellKindedTy`, and not in the
    vocabulary of the generator, and that choice is what makes it provable. `WellKindedTy` is closed under each
    operation the generators perform on context types and is undisturbed by the one way a
    generator extends `C`.

    The proof goes case by case. Only a `cmd` and a `call` grow the scope, and
    `genCmd_outCtx_wellKinded` and `genCallStmt_outCtx_wellKinded` handle them. Only a `typeDecl` changes `C`,
    and it only *adds* a name, which `addKnownTypeWithError_mono` proves. Therefore `WellKindedOk.mono`
    carries the invariant across it. `block`/`ite`/`loop` discard the body's threaded contexts and
    return `C`/`ctx` unchanged, so no recursion into the body is needed and this stands
    outside the soundness `mutual` block. -/
theorem wellKindedOk_preserved
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (hWK : WellKindedOk octx procs C ctx)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n maxStmtSeqLen)) :
    WellKindedOk octx procs r.outC r.outCtx := by
  revert r; show IsSoundFor _ _; walk_genStmt_leaves
  all_goals first
    | exact hWK
    | exact { hWK with
        ctxWK := genCmd_outCtx_wellKinded octx pctx tvars immutableVars hWK.arities ctx _ hWK.ctxWK _ ‹_› }
    | exact WellKindedOk.mono (addKnownTypeWithError_mono ‹_›) hWK
    | exact genCallStmt_outCtx_wellKinded hWK _ ‹_›
    | exact genCallStmtMatch_outCtx_wellKinded hWK _ ‹_›

/-- **`genStmt` changes its context by at most one type declaration.** Every branch but
    `typeDecl` returns its input `C`, and a `typeDecl` returns the result of a successful
    `addKnownTypeWithError`. -/
theorem genStmt_outC_cases
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n maxStmtSeqLen)) :
    r.outC = C ∨ ∃ k f, C.addKnownTypeWithError k f = .ok r.outC := by
  have hcall : ∀ d, IsSoundFor (genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx d pctx)
      (fun r => r.outC = C) := by
    intro d r hr
    cases procs with
    | nil => simp only [genCallStmt, mem_support_bot_iff] at hr
    | cons p₀ ps =>
      simp only [genCallStmt, mem_support_bind_iff] at hr
      obtain ⟨_, _, _, _, hr⟩ := hr
      obtain ⟨_, _, _, _, _, _, rfl⟩ := genCallTail_support hr
      rfl
  revert r; show IsSoundFor _ _; walk_genStmt_leaves
  all_goals first
    | exact .inl rfl
    | exact .inl (hcall _ _ ‹_›)
    | exact .inl (genCallStmtMatch_outC _ ‹_›)
    | exact .inr ⟨_, _, ‹_›⟩

/-- **`genStmt` only extends the known-type table**: a `typeDecl` only adds a name. -/
theorem genStmt_outC_mono
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n maxStmtSeqLen)) :
    ∀ (name : String) (v : Nat), C.knownTypes[name]? = some v →
      r.outC.knownTypes[name]? = some v := by
  rcases genStmt_outC_cases octx pctx tvars immutableVars procs labels C ctx n r hr with
    h | ⟨_, _, h⟩
  · rw [h]
    exact fun _ _ hv => hv
  · exact addKnownTypeWithError_mono h

/-- **`genStmt` keeps the function table**: a `typeDecl` declares a type only. -/
theorem genStmt_outC_functions
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx) (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n maxStmtSeqLen)) :
    r.outC.functions = C.functions := by
  rcases genStmt_outC_cases octx pctx tvars immutableVars procs labels C ctx n r hr with
    h | ⟨_, _, h⟩
  · rw [h]
  · exact addKnownTypeWithError_functions h

mutual

/-- **Soundness of `genStmt`.** Every statement list in the generator's support is well-typed
    (`StatementsWellTyped`, for any program `P` whose callees `procs` describes and whose type
    names are not local type names), from the variable scopes of `env.toTCtx ctx` to those of
    `env.toTCtx r.outCtx`, with the generator's output ambient context `r.outC`. This holds when
    the operators and schemes agree with `C` (`ExprCtxOk`), the scope is functional, and the types
    of the scope, the operators and the written-to blocks of the callees are well kinded in `C`
    (`WellKindedOk`).

    Proved by well-founded recursion on the `size` budget, together with `genStmtChain_sound`. -/
theorem genStmt_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (hProcs : ProcSigCorresponds procs P)
    (hLocalTypes : ∀ n ∈ programNamesOfKind P .type, ¬ isLocalTypeName n.name)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx)
    (hWK : WellKindedOk octx procs C ctx)
    (hops : ExprCtxOk C [] [] octx pctx)
    (n : Nat) (hFun : Map.Functional ctx)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n maxStmtSeqLen)) :
    StatementsWellTyped P C (env.toTCtx ctx).types labels r.stmts r.outC
      (env.toTCtx r.outCtx).types := by
  revert r; show IsSoundFor _ _; rw [IsSoundFor.iff_obs]
  cases n <;> rw [genStmt] <;>
    walk [(isSoundFor_self_support (genCmdStmt _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genExitStmt _ _ _)).obs,
      (isSoundFor_self_support (genTypeDeclStmt _ _ _)).obs,
      (isSoundFor_self_support (genCallStmt _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genCallStmtMatch _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genFreshLabel _)).obs,
      (isSoundFor_self_support (genStmtChain _ _ _ _ _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genLExpr _ _ _ _ _ _ _)).obs,
      (isSoundFor_self_support (genCondOrNondet _ _ _ _ _)).obs,
      (isSoundFor_self_support (genOptMeasure _ _ _ _ _)).obs,
      (isSoundFor_self_support (genInvariants _ _ _ _ _ _)).obs]
  all_goals first
    | exact genCmdStmt_sound P env C hops ctx _ hFun _ ‹_›
    | exact genExitStmt_sound P env C ctx _ ‹_›
    | exact genTypeDeclStmt_sound P env hLocalTypes C ctx _ _ ‹_›
    | exact genCallStmt_sound P env _ hProcs C ctx _ hWK hops hFun _ ‹_›
    | exact genCallStmtMatch_sound P env _ hProcs C ctx _ hWK hops hFun _ ‹_›
    | exact StatementsWellTyped_singleton (.block C _ _ _ labels _ _ default _
        (genFreshLabel_not_mem labels _ ‹_›)
        (genStmtChain_sound P env immutableVars procs hProcs hLocalTypes _ C ctx hWK hops _ _ hFun _ ‹_›)
        (Strata.Util.HMaps.Equiv.refl _))
    | exact StatementsWellTyped_singleton (.ite_det C _ _ _ _ _ labels _ _ _ default _
        (env.exprWellTyped hops hFun hWK.ctxWK (knownInstance_bool hops.arities) ‹_›)
        (genStmtChain_sound P env immutableVars procs hProcs hLocalTypes labels C ctx hWK hops _ _ hFun _ ‹_›)
        (genStmtChain_sound P env immutableVars procs hProcs hLocalTypes labels C ctx hWK hops _ _ hFun _ ‹_›)
        (Strata.Util.HMaps.Equiv.refl _))
    | exact StatementsWellTyped_singleton (.ite_nondet C _ _ _ _ _ labels _ _ default _
        (genStmtChain_sound P env immutableVars procs hProcs hLocalTypes labels C ctx hWK hops _ _ hFun _ ‹_›)
        (genStmtChain_sound P env immutableVars procs hProcs hLocalTypes labels C ctx hWK hops _ _ hFun _ ‹_›)
        (Strata.Util.HMaps.Equiv.refl _))
    | exact StatementsWellTyped_singleton (.loop C _ _ _ labels _ _ _ _ default _
        (genCondOrNondet_det_sound env _ ctx _ hops hFun hWK.ctxWK ‹_›)
        (genOptMeasure_some_sound env _ ctx _ hops hFun hWK.ctxWK ‹_›)
        (genInvariants_sound env _ _ ctx _ hops hFun hWK.ctxWK ‹_›)
        (genStmtChain_sound P env immutableVars procs hProcs hLocalTypes labels C ctx hWK hops _ _ hFun _ ‹_›)
        (Strata.Util.HMaps.Equiv.refl _))
termination_by (n, 0, 0)

/-- **Soundness of `genStmtChain`.** Every statement sequence in the generator's support is
    well-typed (`StatementsWellTyped`) between the input scopes and the generator's threaded
    output contexts, when every callable procedure resolves in `P`, no type name of `P` is a local
    type name, the operator, callee and scope types are well kinded in `C`, the operators and
    schemes agree with `C`, and the scope is functional. Proved by well-founded recursion on the
    remaining length `len`. -/
theorem genStmtChain_sound (P : Program) (env : GenStmtSoundEnv octx tvars pctx)
    (immutableVars : List (Identifier Unit)) (procs : ProcSigCtx)
    (hProcs : ProcSigCorresponds procs P)
    (hLocalTypes : ∀ n ∈ programNamesOfKind P .type, ¬ isLocalTypeName n.name)
    (labels : List String) (C : LContext CoreLParams) (ctx : VarCtx)
    (hWK : WellKindedOk octx procs C ctx)
    (hops : ExprCtxOk C [] [] octx pctx)
    (size len : Nat) (hFun : Map.Functional ctx)
    (result : List Statement × LContext CoreLParams × VarCtx)
    (hr : result ∈ SPMF.support
      (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size len maxStmtSeqLen)) :
    StatementsWellTyped P C (env.toTCtx ctx).types labels result.1 result.2.1
      (env.toTCtx result.2.2).types := by
  revert result; show IsSoundFor _ _; rw [IsSoundFor.iff_obs]
  cases len <;> rw [genStmtChain] <;> walk [(isSoundFor_self_support (genStmt _ _ _ _ _ _ _ _ _ _)).obs,
    (isSoundFor_self_support (genStmtChain _ _ _ _ _ _ _ _ _ _ _)).obs]
  · exact .nil C _ labels _ (Strata.Util.HMaps.Equiv.refl _)
  · exact StatementsWellTyped_append
      (genStmt_sound P env immutableVars procs hProcs hLocalTypes labels C ctx hWK hops size hFun _ ‹_›)
      (genStmtChain_sound P env immutableVars procs hProcs hLocalTypes labels _ _
        (wellKindedOk_preserved octx pctx tvars immutableVars procs labels C ctx size hWK _ ‹_›)
        (hops.mono (genStmt_outC_functions octx pctx tvars immutableVars procs labels C ctx size _ ‹_›)
          (genStmt_outC_mono octx pctx tvars immutableVars procs labels C ctx size _ ‹_›))
        size _
        (genStmt_outCtx_functional octx pctx tvars immutableVars procs labels C ctx size hFun _ ‹_›)
        _ ‹_›)
termination_by (size, 1, len)

end

-- ── Membership-lifting lemmas (for completeness) ─────────────────────────
-- These lift a result from a sub-generator's support into `genStmt`'s support.
-- Every branch of the `frequency` list has positive weight, so its support is
-- contained in `genStmt`'s support; these lemmas package the reconstruction.
--
-- With the single `size` budget, the leaf sub-generators are invoked at *the same*
-- size `n` as `genStmt` itself (`genStmt … n` calls `genCmdStmt … n`), so the leaf
-- `_mem` lemmas take a result at depth `n` and land in `genStmt … n`.

/-- A `genCmdStmt` result (at depth `n`) is reachable by `genStmt … n`. -/
theorem genCmdStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support (genCmdStmt (G := SPMF) octx tvars immutableVars C ctx n pctx)) :
    r ∈ SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n maxStmtSeqLen) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
    exact ⟨4, _, .head _, by omega, hr⟩
  | succ size =>
    rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
    exact ⟨7, _, .head _, by omega, hr⟩

/-- A `genExitStmt` result is reachable by `genStmt … n` at *every* size `n`. -/
theorem genExitStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support (genExitStmt (G := SPMF) labels C ctx)) :
    r ∈ SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n maxStmtSeqLen) := by
  -- With `labels = []` the `exit` branch is weighted 0, but there `genExitStmt`
  -- is `default` (support `∅`), so `hr` is impossible; with `labels ≠ []` the
  -- branch weight reduces to `1`.
  cases labels with
  | nil => simp only [genExitStmt, SPMF.mem_support_bot_iff] at hr
  | cons hd tl =>
    cases n with
    | zero =>
      rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
      exact ⟨_, _, .tail _ (.head _), by simp, hr⟩
    | succ size =>
      rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
      exact ⟨_, _, .tail _ (.head _), by simp, hr⟩

/-- A `genTypeDeclStmt` result (at depth `n`) is reachable by `genStmt … n`. -/
theorem genTypeDeclStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support (genTypeDeclStmt (G := SPMF) C ctx n)) :
    r ∈ SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n maxStmtSeqLen) := by
  cases n with
  | zero =>
    rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.head _)), by omega, hr⟩
  | succ size =>
    rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
    exact ⟨1, _, .tail _ (.tail _ (.head _)), by omega, hr⟩

/-- A `genCallStmt` result (at depth `n`) is reachable by `genStmt … n`. The call
    branch sits at frequency index 3 in both the size-0 and size+1 lists. -/
theorem genCallStmt_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support (genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx n pctx)) :
    r ∈ SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n maxStmtSeqLen) := by
  -- With `procs = []` the `call` branch is weighted 0, but there `genCallStmt`
  -- is `default` (support `∅`), so `hr` is impossible; with `procs ≠ []` the
  -- branch weight reduces to `1`.
  cases procs with
  | nil => simp only [genCallStmt, SPMF.mem_support_bot_iff] at hr
  | cons hd tl =>
    cases n with
    | zero =>
      rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
      exact ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by simp, hr⟩
    | succ size =>
      rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
      exact ⟨_, _, .tail _ (.tail _ (.tail _ (.head _))), by simp, hr⟩

/-- A `block` statement is reachable by `genStmt … (size+1)` when its body (of some
    length `len ≤ size+1`) is reachable by `genStmtChain … size` under the extended
    label scope `label :: labels`. -/
theorem block_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (label : String) (body : List Statement) (C_body : LContext CoreLParams) (Γ_body : VarCtx)
    (len : Nat) (hlen : len ≤ maxStmtSeqLen)
    (hbody : (body, C_body, Γ_body) ∈
      SPMF.support (genStmtChain (G := SPMF) octx tvars immutableVars procs (label :: labels) C ctx pctx size len maxStmtSeqLen))
    (hlabel : label ∈ SPMF.support (genFreshLabel (G := SPMF) labels)) :
    (⟨[Stmt.block label body default], C, ctx⟩ : GenStmtResult) ∈
      SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx (size + 1) maxStmtSeqLen) := by
  rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
  refine ⟨1, _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨label, hlabel, ⟨⟨len, Nat.zero_le _, hlen⟩⟩, trivial,
    (body, C_body, Γ_body), hbody, rfl⟩

/-- An `ite (.det cond)` statement is reachable by `genStmt … (size+1)` when the
    condition is a reachable boolean (at depth `size+1`), and both branches are reachable by
    `genStmtChain … size`. -/
theorem ite_det_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (cond : Expression.Expr) (thenb elseb : List Statement)
    (Ct : LContext CoreLParams) (Γt : VarCtx) (Ce : LContext CoreLParams) (Γe : VarCtx)
    (tlen elen : Nat) (htlen : tlen ≤ maxStmtSeqLen) (helen : elen ≤ maxStmtSeqLen)
    (hcond : cond ∈ SPMF.support (genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] (size + 1) .bool))
    (hthen : (thenb, Ct, Γt) ∈
      SPMF.support (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size tlen maxStmtSeqLen))
    (helse : (elseb, Ce, Γe) ∈
      SPMF.support (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size elen maxStmtSeqLen)) :
    (⟨[Stmt.ite (.det cond) thenb elseb default], C, ctx⟩ : GenStmtResult) ∈
      SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx (size + 1) maxStmtSeqLen) := by
  rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
  refine ⟨1, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨cond, hcond, ⟨⟨tlen, Nat.zero_le _, htlen⟩⟩, trivial,
    ⟨⟨elen, Nat.zero_le _, helen⟩⟩, trivial,
    (thenb, Ct, Γt), hthen, (elseb, Ce, Γe), helse, rfl⟩

/-- An `ite .nondet` statement is reachable by `genStmt … (size+1)` when both
    branches are reachable by `genStmtChain … size`. -/
theorem ite_nondet_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (thenb elseb : List Statement)
    (Ct : LContext CoreLParams) (Γt : VarCtx) (Ce : LContext CoreLParams) (Γe : VarCtx)
    (tlen elen : Nat) (htlen : tlen ≤ maxStmtSeqLen) (helen : elen ≤ maxStmtSeqLen)
    (hthen : (thenb, Ct, Γt) ∈
      SPMF.support (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size tlen maxStmtSeqLen))
    (helse : (elseb, Ce, Γe) ∈
      SPMF.support (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size elen maxStmtSeqLen)) :
    (⟨[Stmt.ite .nondet thenb elseb default], C, ctx⟩ : GenStmtResult) ∈
      SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx (size + 1) maxStmtSeqLen) := by
  rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
  refine ⟨1, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨⟨⟨tlen, Nat.zero_le _, htlen⟩⟩, trivial,
    ⟨⟨elen, Nat.zero_le _, helen⟩⟩, trivial,
    (thenb, Ct, Γt), hthen, (elseb, Ce, Γe), helse, rfl⟩

/-- A `loop` statement is reachable by `genStmt … (size+1)` when its guard, measure,
    invariants (all at depth `size+1`), and body (by `genStmtChain … size`) are all
    reachable. -/
theorem loop_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat)
    (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
    (invs : List (String × Expression.Expr)) (body : List Statement)
    (C_body : LContext CoreLParams) (Γ_body : VarCtx)
    (blen : Nat) (hblen : blen ≤ maxStmtSeqLen)
    (hguard : guard ∈ SPMF.support
      (genCondOrNondet (G := SPMF) octx tvars ctx (size + 1) pctx))
    (hmeasure : measure ∈ SPMF.support
      (genOptMeasure (G := SPMF) octx tvars ctx (size + 1) pctx))
    (hinvs : invs ∈ SPMF.support
      (genInvariants (G := SPMF) octx tvars ctx maxStmtSeqLen (size + 1) pctx))
    (hbody : (body, C_body, Γ_body) ∈
      SPMF.support (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size blen maxStmtSeqLen)) :
    (⟨[Stmt.loop guard measure invs body default], C, ctx⟩ : GenStmtResult) ∈
      SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx (size + 1) maxStmtSeqLen) := by
  rw [genStmt, mem_support_frequency_iff (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega)]
  refine ⟨1, _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))), by omega, ?_⟩
  simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff]
  exact ⟨guard, hguard, measure, hmeasure, invs, hinvs,
    ⟨⟨blen, Nat.zero_le _, hblen⟩⟩, trivial,
    (body, C_body, Γ_body), hbody, rfl⟩

-- ── genStmtChain membership: cons / nil ──────────────────────────────────────

/-- The empty statement list is in `genStmtChain`'s support at length `0`. -/
theorem genStmtChain_nil_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size : Nat) :
    ((([] : List Statement)), C, ctx) ∈
      SPMF.support (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size 0 maxStmtSeqLen) := by
  rw [genStmtChain]; exact mem_support_pure_iff.mpr rfl

/-- If the head statement `r` is reachable by `genStmt` (at `size`) and the tail is
    reachable by `genStmtChain` from the head's output contexts (at the same `size`,
    length `len`), then the whole `cons` is reachable at length `len+1`. -/
theorem genStmtChain_cons_mem (procs : ProcSigCtx) (C : LContext CoreLParams) (ctx : VarCtx) (size len : Nat)
    (r : GenStmtResult) (rest : List Statement) (C'' : LContext CoreLParams) (Γ'' : VarCtx)
    (hhead : r ∈ SPMF.support (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size maxStmtSeqLen))
    (htail : (rest, C'', Γ'') ∈
      SPMF.support (genStmtChain (G := SPMF) octx tvars immutableVars procs labels r.outC r.outCtx pctx size len maxStmtSeqLen)) :
    (r.stmts ++ rest, C'', Γ'') ∈
      SPMF.support (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size (len + 1) maxStmtSeqLen) := by
  rw [genStmtChain]
  simp only [mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨r, hhead, (rest, C'', Γ''), htail, rfl⟩

-- ── Completeness helper lemmas ────────────────────────────────────────────
-- Straightforward `pick`/`map`/`listOfMaxLength` support-inversion lemmas, one
-- per guard/measure/invariant/type-constructor sub-generator, mirroring
-- `genOptExpr_complete` in `FunctionHasTypeAGen.lean`. These convert typed
-- side-conditions into raw support-membership facts consumed by the spec-indexed
-- completeness proof (`StmtHasTypeAGenComplete.lean`). Each is stated at an arbitrary depth.

/-- Completeness of `genCondOrNondet`. `.nondet` is always reachable; `.det g` is
    reachable when `g` is reachable by `genLExpr` at type `bool`. -/
theorem genCondOrNondet_complete (depth : Nat) (ctx : VarCtx)
    (cond : ExprOrNondet Expression)
    (hcond : ∀ g, cond = .det g →
      g ∈ SPMF.support (genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] depth .bool)) :
    cond ∈ SPMF.support (genCondOrNondet (G := SPMF) octx tvars ctx depth pctx) := by
  rw [genCondOrNondet, mem_support_frequency_iff]
  cases cond with
  | nondet =>
    -- weight-1 `.nondet` branch
    exact ⟨1, _, List.mem_cons_self, by omega, mem_support_pure_iff.mpr rfl⟩
  | det g =>
    -- weight-4 `.det` branch
    exact ⟨4, _, List.mem_cons_of_mem _ List.mem_cons_self, by omega,
      mem_support_map_iff.mpr ⟨g, hcond g rfl, rfl⟩⟩

/-- Completeness of `genOptMeasure`. `none` is always reachable; `some m` is
    reachable when `m` is reachable by `genLExpr` at type `int`. -/
theorem genOptMeasure_complete (depth : Nat) (ctx : VarCtx)
    (measure : Option Expression.Expr)
    (hmeasure : ∀ m, measure = some m →
      m ∈ SPMF.support (genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] depth .int)) :
    measure ∈ SPMF.support (genOptMeasure (G := SPMF) octx tvars ctx depth pctx) := by
  simp only [genOptMeasure,
    mem_support_biasedOptionGen_iff (r := 3/4) (by decide +kernel) (by decide +kernel)]
  cases measure with
  | none => exact Or.inl rfl
  | some m => exact Or.inr ⟨m, hmeasure m rfl, rfl⟩

/-- Completeness of `genInvariant`. A `(label, e)` pair is reachable when the
    label is a reachable identifier (via `genIdentName`, so non-empty and
    non-keyword) and `e` is a reachable boolean. -/
theorem genInvariant_complete (depth : Nat) (ctx : VarCtx)
    (p : String × Expression.Expr)
    (hlabel : p.1 ∈ SPMF.support (genIdentName (G := SPMF)))
    (hexpr : p.2 ∈ SPMF.support
      (genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] depth .bool)) :
    p ∈ SPMF.support (genInvariant (G := SPMF) octx tvars ctx depth pctx) := by
  simp only [genInvariant, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨p.1, hlabel, p.2, hexpr, rfl⟩

/-- The completeness of `genInvariants`. A list of the invariants is reachable when its length is not more than
    `maxLen`, and each of its elements is reachable by `genInvariant`. -/
theorem genInvariants_complete (maxLen depth : Nat) (ctx : VarCtx)
    (invs : List (String × Expression.Expr))
    (hlen : invs.length ≤ maxLen)
    (hinvs : ∀ p ∈ invs, p.1 ∈ SPMF.support (genIdentName (G := SPMF)) ∧
      p.2 ∈ SPMF.support
        (genLExpr (G := SPMF) ctx.toFVarCtx octx pctx tvars [] depth .bool)) :
    invs ∈ SPMF.support (genInvariants (G := SPMF) octx tvars ctx maxLen depth pctx) := by
  simp only [genInvariants, mem_support_listOfMaxLength_iff]
  refine ⟨hlen, fun p hp => ?_⟩
  exact genInvariant_complete depth ctx p (hinvs p hp).1 (hinvs p hp).2

/-- Every local type name that `genIdentName` can draw is reachable by `genLocalTypeName`. -/
theorem genLocalTypeName_complete {s : String}
    (hs : s ∈ SPMF.support (genIdentName (G := SPMF)))
    (hlocal : isLocalTypeName s = true) :
    s ∈ SPMF.support (genLocalTypeName (G := SPMF)) := by
  simp only [genLocalTypeName, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨s, hs, by simp only [hlocal, ite_true]⟩

/-- The completeness of `genTypeConstructor`. A type constructor is reachable when its name is a
    local type name, its name and each of its parameter names is a reachable identifier of
    `genIdentName`, and its parameter list is no longer than the depth. -/
theorem genTypeConstructor_complete (depth : Nat) (tc : TypeConstructor)
    (hlocal : isLocalTypeName tc.name = true)
    (hname : tc.name ∈ SPMF.support (genIdentName (G := SPMF)))
    (hlen : tc.params.length ≤ depth)
    (hparams : ∀ s ∈ tc.params, s ∈ SPMF.support (genIdentName (G := SPMF))) :
    tc ∈ SPMF.support (genTypeConstructor (G := SPMF) depth) := by
  simp only [genTypeConstructor, mem_support_bind_iff, mem_support_pure_iff,
             mem_support_listOfMaxLength_iff]
  refine ⟨tc.name, genLocalTypeName_complete hname hlocal, tc.params, ⟨hlen, hparams⟩, tc.bound,
    ?_, ?_⟩
  · -- both `Boundedness` values are in the sampled list
    rw [mem_support_elements_iff]; cases tc.bound <;> simp
  · obtain ⟨bound, name, params⟩ := tc; rfl

/-- `genTypeConstructor_complete`, and `mem_support_genIdentName_iff` discharges both of its
    hypotheses on name reachability from syntax. Only decidable conditions remain: the name of the
    constructor is a local type name, and it and each parameter name is a bare Core identifier and
    is not a reserved keyword. -/
theorem genTypeConstructor_complete_of_syntactic (depth : Nat) (tc : TypeConstructor)
    (hlocal : isLocalTypeName tc.name = true)
    (hnameSyn : StrataGenerators.Function.IsGenIdentName tc.name)
    (hnameKw : isReservedKeyword tc.name = false)
    (hlen : tc.params.length ≤ depth)
    (hparams : ∀ s ∈ tc.params,
      StrataGenerators.Function.IsGenIdentName s ∧ isReservedKeyword s = false) :
    tc ∈ SPMF.support (genTypeConstructor (G := SPMF) depth) :=
  genTypeConstructor_complete depth tc hlocal
    (StrataGenerators.Function.mem_support_genIdentName_of_syntactic hnameSyn hnameKw) hlen
    (fun s hs => StrataGenerators.Function.mem_support_genIdentName_of_syntactic
      (hparams s hs).1 (hparams s hs).2)

end StrataGenerators.Stmt
