import StrataGenerators.StmtHasTypeAGen
import StrataGenerators.CmdHasTypeAGenSound
import Strata.Languages.Core.Procedure

open Lambda LExpr RandomChoice Core Imperative TypeSpec
open StrataGenerators.Stmt

/-!
# The modification-rights invariant for the statement generator

`ProcHasType'.modRights` requires that every variable a procedure body *modifies*
is either an output parameter or is *defined* somewhere in the body:

    ∀ v ∈ modifiedVars body, v ∈ outputs.keys ++ definedVars body false.

`genProcedure` builds its body via `genStmtChain`, seeding the threaded `VarCtx` with
exactly the procedure's output parameters. So it suffices to prove the more
general invariant that, for any generated statement (sequence) threaded from an
arbitrary starting context `ctx`,

    ∀ v ∈ modifiedVars s, v ∈ ctx.keys ++ definedVars s false,

together with the auxiliary key-tracking fact that every key of the *output*
context is likewise accounted for by `ctx.keys ++ definedVars s false`. The two
must be proved *together*: threading a statement sequence grows the context, and
the tail's modified variables are justified against the head's *output* keys,
which the auxiliary fact ties back to `ctx.keys ++ definedVars`.

## Why the invariant holds structurally

- The one command that *modifies* a variable is `set`. `elements` draws its target from the *mutable* part of
  the scope, which is `ctx.writable immutableVars`, so that target is always a key of that part. Therefore no
  command modifies an immutable name, which is an input of the procedure.
- The only command that *grows* the context is `init`, which both defines the
  new name (`definedVars = [name]`) and adds it as a mutable key.
- The nesting statements (`block`, `ite`, `loop`) are lexically scoped: their
  output `VarCtx` is the *input* `ctx` (the body's threaded scope is discarded),
  and both `modifiedVars` and `definedVars _ false` descend into the body
  in the same way. Therefore a `set` can never target a variable that lives inside a nested block of a sibling
  statement, and the body of the recursion keeps the invariant.
- `genCmd` emits no `.call`. Each `.call` comes from `genCallStmt`, and its group writes to the in-out names of
  the callee and to the out targets. Each of those names comes from the scope, and the `usable` guard makes it
  writable, or the inline chain of the `init` statements of the group declares it. Therefore each of them is a
  key of the scope or a name that the group defines. This branch is also the one branch whose output scope is
  *larger* than its input scope, which is `insertAllCtx ctx toInit`, because the `init` statements are inline and
  no block holds them,
  and the names it adds are exactly its `definedVars`.

The modified keys and the tracked keys are the keys of the *mutable* part of the scope. Therefore, at the top
level, where the scope is the inputs and the outputs and the immutable names are the keys of the inputs, the
set becomes the keys of the outputs. That set is exactly the obligation `ProcHasType'.modRights`, and no input
key enters it, because `writable` removes each of them.

## Statement lists

`genStmt` returns a statement **list** (a singleton except for the `call` group),
so the invariant is stated at `Block.modifiedVars` / `Block.definedVars` over the
list rather than at the single-statement `HasVarsImp` projections. The eight
singleton branches reduce to the old single-statement reasoning via
`block_modifiedVars_singleton` / `block_definedVars_singleton`, and the chain's
`cons` case **appends** the head group (`block_*_append`) instead of consing it.
-/

namespace StrataGenerators.Procedure

/-- Membership in the *mutable* sub-context's keys: `k` is a mutable key iff it
    is a key of the full context **and** is not a immutable name. This is the
    single bridge that turns the write-target-tracking into the
    `modRights` obligation (at the top level `ctx.writable inputs.keys` drops
    exactly the input keys, leaving the output keys). -/
theorem mem_writable_keys_iff (ctx : VarCtx) (immutableVars : List (Identifier Unit))
    (k : Identifier Unit) :
    k ∈ Map.keys (ctx.writable immutableVars) ↔ k ∈ Map.keys ctx ∧ (!immutableVars.contains k) = true := by
  rw [Map.keys_eq_map_fst (ctx.writable immutableVars), Map.keys_eq_map_fst ctx]
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    obtain ⟨hp_mem, hp_pred⟩ := List.mem_filter.mp hp
    exact ⟨List.mem_map_of_mem hp_mem, hp_pred⟩
  · rintro ⟨h, hpred⟩
    obtain ⟨p, hp_mem, rfl⟩ := List.mem_map.mp h
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hp_mem, hpred⟩)

/-- The mutable keys after an `init` of `n` are the old mutable keys and `n`. -/
private theorem init_writable_keys {ctx : VarCtx} {iv : List (Identifier Unit)} {n mty k ty e md}
    (hk : k ∈ Map.keys (VarCtx.writable iv (Map.insert ctx n mty))) :
    k ∈ Map.keys (ctx.writable iv) ++
      HasVarsImp.definedVars (P := Expression) (Cmd.init (P := Expression) n ty e md) false := by
  obtain ⟨hk_keys, hk_ro⟩ := (mem_writable_keys_iff _ _ k).mp hk
  rcases List.mem_cons.mp (Map.insert_keys ctx hk_keys) with rfl | h
  · exact List.mem_append_right _ (by simp [HasVarsImp.definedVars, Cmd.definedVars])
  · exact List.mem_append_left _ ((mem_writable_keys_iff ctx iv k).mpr ⟨h, hk_ro⟩)

/-- The target of a `set` drawn from the mutable sub-context is a mutable key. -/
private theorem set_modified {ctx : VarCtx} {iv : List (Identifier Unit)} {r : Identifier Unit × LMonoTy}
    {v e md} {D : List _} (hr : List.Mem r (ctx.writable iv))
    (hv : v ∈ HasVarsImp.modifiedVars (P := Expression) (Cmd.set (P := Expression) r.1 e md)) :
    v ∈ Map.keys (ctx.writable iv) ++ D := by
  simp only [HasVarsImp.modifiedVars, Cmd.modifiedVars, List.mem_singleton] at hv
  exact List.mem_append_left _ (hv ▸ Map.keys_eq_map_fst _ ▸ List.mem_map_of_mem hr)

/-- **Per-command modification-rights invariant.** For any command in `genCmd`'s
    support, every modified variable is a *mutable* key of the input context
    (all modified variables come from `set`, whose target is drawn from
    `elements (ctx.writable immutableVars)`), and every mutable output-context key is
    either a mutable input key or the freshly-`init`-defined name. -/
theorem genCmd_mutableVars
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat) {avoid : List String}
    {kt : Lambda.KnownTypes} (r : GenCmdResult)
    (hr : r ∈ SPMF.support
      (genCmd (G := SPMF) octx tvars immutableVars ctx depth pctx avoid kt)) :
    (∀ v ∈ HasVarsImp.modifiedVars (P := Expression) r.cmd,
      v ∈ Map.keys (ctx.writable immutableVars) ++ HasVarsImp.definedVars (P := Expression) r.cmd false) ∧
    (∀ k ∈ Map.keys (r.outCtx.writable immutableVars),
      k ∈ Map.keys (ctx.writable immutableVars) ++ HasVarsImp.definedVars (P := Expression) r.cmd false) := by
  revert r; show IsSoundFor _ _; walk_genCmd
  all_goals try split_ifs at *
  all_goals first
    | exact List.mem_append_left _ ‹_›
    | exact init_writable_keys ‹_›
    | exact set_modified ‹_› ‹_›
    | simp [HasVarsImp.modifiedVars, Cmd.modifiedVars] at *

-- ── Membership-monotonicity helpers ──────────────────────────────────────

/-! These are pure list-membership bookkeeping over nested appends; `grind`
discharges each from the `List.mem_append` case split, so none needs a manual
proof. They are kept as *named* lemmas because they document the four distinct
shapes the invariant proofs below reason in, and let those proofs read as one
`exact` apiece. -/

/-- Grow the *defined-set* summand on the right of an `xs ++ ys` membership. -/
theorem mem_append_grow_r {α} (v : α) (xs ys zs : List α)
    (h : v ∈ xs ++ ys) : v ∈ xs ++ (ys ++ zs) := by grind

/-- Insert a middle summand into an `xs ++ zs` membership. -/
theorem mem_append_grow_mid {α} (v : α) (xs ys zs : List α)
    (h : v ∈ xs ++ zs) : v ∈ xs ++ (ys ++ zs) := by grind

/-- Chain a threaded modified/key fact through a sequence step: something
    accounted for by the *tail's* context `B ++ defT`, where every element of `B`
    is itself accounted for by `xs ++ defH`, is accounted for by
    `xs ++ (defH ++ defT)`. -/
theorem trans_step {α} (x : α) (B xs defH defT : List α)
    (hB : ∀ y ∈ B, y ∈ xs ++ defH)
    (hx : x ∈ B ++ defT) : x ∈ xs ++ (defH ++ defT) := by grind

/-- Combine the two branches of an `ite` (whose output scope is the input `ctx`):
    the concatenated modified-set is justified by the concatenated defined-set.
    Stated over an arbitrary key list `keys` (instantiated at
    `Map.keys (ctx.writable immutableVars)`). -/
theorem ite_combine (keys : List Expression.Ident)
    (modT modE defT defE : List Expression.Ident)
    (hT : ∀ v ∈ modT, v ∈ keys ++ defT)
    (hE : ∀ v ∈ modE, v ∈ keys ++ defE) :
    (∀ v ∈ modT ++ modE, v ∈ keys ++ (defT ++ defE)) := by grind

-- ── Write-set of a generated procedure-call block ─────────────────────────

/-! `Block.modifiedVars` and `Block.definedVars` are defined by the recursion
`s :: rest ↦ f s ++ go rest`, which is exactly `List.flatMap`. Rather than
a separate induction for each structural fact, such as the distribution over an append and the behaviour on a
list from a `map`, this file proves the description as a `flatMap` **one time** below, and it then takes each
such fact from the standard library
(`List.flatMap_append`, `List.flatMap_map`, `List.flatMap_eq_nil_iff`,
`List.map_eq_flatMap`, `List.mem_flatMap`, …). The two bridge lemmas are the only
inductions needed. -/

/-- `Block.modifiedVars` is `List.flatMap Stmt.modifiedVars`. -/
theorem block_modifiedVars_eq_flatMap (ss : List Statement) :
    Block.modifiedVars (P := Expression) ss
      = ss.flatMap (Stmt.modifiedVars (P := Expression)) := by
  induction ss with
  | nil => rfl
  | cons hd tl ih => simp only [Block.modifiedVars, List.flatMap_cons, ih]

/-- `Block.definedVars` is `List.flatMap (Stmt.definedVars · b)`. -/
theorem block_definedVars_eq_flatMap (ss : List Statement) (b : Bool) :
    Block.definedVars (P := Expression) ss b
      = ss.flatMap (fun s => Stmt.definedVars (P := Expression) s b) := by
  induction ss with
  | nil => simp only [Block.definedVars, List.flatMap_nil]
  | cons hd tl ih => simp only [Block.definedVars, List.flatMap_cons, ih]

/-- `Block.modifiedVars` distributes over list append (`List.flatMap_append`). -/
theorem block_modifiedVars_append (xs ys : List Statement) :
    Block.modifiedVars (P := Expression) (xs ++ ys)
      = Block.modifiedVars (P := Expression) xs ++ Block.modifiedVars (P := Expression) ys := by
  simp only [block_modifiedVars_eq_flatMap, List.flatMap_append]

/-- `Block.definedVars _ false` distributes over list append (`List.flatMap_append`). -/
theorem block_definedVars_append (xs ys : List Statement) :
    Block.definedVars (P := Expression) (xs ++ ys) false
      = Block.definedVars (P := Expression) xs false ++ Block.definedVars (P := Expression) ys false := by
  simp only [block_definedVars_eq_flatMap, List.flatMap_append]

/-! Every `genStmt` branch but `call` returns a *singleton* list, so the two lemmas
below are the bridge that lets the eight single-statement branches be discharged
exactly as they were before `genStmt` returned a list. -/

/-- A singleton statement list modifies what its one statement modifies. -/
@[simp] theorem block_modifiedVars_singleton (s : Statement) :
    Block.modifiedVars (P := Expression) [s] = Stmt.modifiedVars (P := Expression) s := by
  simp only [Block.modifiedVars, List.append_nil]

/-- A singleton statement list defines what its one statement defines. -/
@[simp] theorem block_definedVars_singleton (s : Statement) (b : Bool) :
    Block.definedVars (P := Expression) [s] b = Stmt.definedVars (P := Expression) s b := by
  simp only [Block.definedVars, List.append_nil]

/-- The chain of the `init … nondet` statements modifies nothing. Each statement of it is an `init`, and an
    `init` modifies nothing, so the `flatMap` gives the empty list at each element. -/
theorem initChain_modifiedVars (news : List (Identifier Unit × LMonoTy)) :
    Block.modifiedVars (P := Expression) (StrataGenerators.Stmt.initChain news) = [] := by
  simp only [block_modifiedVars_eq_flatMap, StrataGenerators.Stmt.initChain, List.flatMap_map]
  exact List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)

/-- The `init … nondet` chain defines exactly the declared names: each `init`
    contributes the singleton `[x]`, and `flatMap` of a singleton is `map`. -/
theorem initChain_definedVars (news : List (Identifier Unit × LMonoTy)) :
    Block.definedVars (P := Expression) (StrataGenerators.Stmt.initChain news) false
      = news.map Prod.fst := by
  simp only [block_definedVars_eq_flatMap, StrataGenerators.Stmt.initChain, List.flatMap_map,
    Stmt.definedVars, HasVarsImp.definedVars]
  exact (List.map_eq_flatMap ..).symm

/-- The *group* of a generated procedure call, which is the inline chain of the `init` statements followed by the
    `call`, as a statement **list**, modifies exactly the in-out names and the chosen out targets. That set does
    not depend on which of those names the group declares. The chain at the front modifies nothing, and the
    `call` modifies its written-to names, which are
    (`getLhs_mkArgs = M.keys ++ T.keys`). -/
theorem callGroup_modifiedVars (M T : @LMonoTySignature Unit) (pname : String)
    (missing : List (Identifier Unit × LMonoTy))
    (exprs : List Expression.Expr) (mask : List Bool) :
    Block.modifiedVars (P := Expression)
      (StrataGenerators.Stmt.initChain missing ++
        [Statement.call pname (StrataGenerators.Stmt.mkArgs M T exprs mask) default])
      = M.keys ++ T.keys := by
  rw [block_modifiedVars_append, initChain_modifiedVars]
  simp only [List.nil_append, Block.modifiedVars, Stmt.modifiedVars, HasVarsImp.modifiedVars,
    CmdExt.modifiedVars, StrataGenerators.Stmt.getLhs_mkArgs, List.append_nil]

/-- The generated procedure-call group defines exactly the `init`ed names
    the names of the missing entries. The chain at the front declares each of them, and the `call` defines
    nothing. No `block` holds those names, so they enter the scope around the group. That is why the output scope
    of the group is `insertAllCtx ctx missing`, and not the input scope. -/
theorem callGroup_definedVars (M T : @LMonoTySignature Unit) (pname : String)
    (missing : List (Identifier Unit × LMonoTy))
    (exprs : List Expression.Expr) (mask : List Bool) :
    Block.definedVars (P := Expression)
      (StrataGenerators.Stmt.initChain missing ++
        [Statement.call pname (StrataGenerators.Stmt.mkArgs M T exprs mask) default]) false
      = missing.map Prod.fst := by
  rw [block_definedVars_append, initChain_definedVars]
  simp only [Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars,
    List.append_nil]

/-- A required name `v ∈ M.keys ++ T.keys` is a key of `M ++ T`, the variables the
    call writes to.
    Bridges from the `getLhs_mkArgs` write-set (`M.keys ++ T.keys`) back to the
    in-out block and out targets the generator reasons about. -/
theorem mem_keys_append_exists (M T : @LMonoTySignature Unit) (v : Identifier Unit)
    (hv : v ∈ M.keys ++ T.keys) :
    ∃ q : Identifier Unit × LMonoTy, q ∈ List.append M T ∧ q.1 = v := by
  -- A key of either block is the first component of one of that block's entries.
  rcases List.mem_append.mp hv with h | h
  · rw [ListMap.keys_eq_map_fst M] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    exact ⟨q, List.mem_append_left _ hq, rfl⟩
  · rw [ListMap.keys_eq_map_fst T] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    exact ⟨q, List.mem_append_right _ hq, rfl⟩

/-- **The invariant about the rights to modify a variable, for one call statement.** The emitted group is the
    inline chain of the `init` statements followed by the `call`, as a statement *list*, and the generator splices
    it into the scope around it, with no `block`. Each modified variable of that group is a written-to name of the
    call. Each of them is a *mutable* key of the input scope, or a name that the group defines:

    * A name that the group *reuses* is bound in the scope **and** is not immutable, which the `usable` guard
      gives, and `outTargets_all_usableName` gives for an out target. Therefore it is a key of
      `ctx.writable immutableVars`.
    * A name that the scope does not hold is a fresh in-out name or a new out target, and the inline chain
      declares it. When the group needs no declaration, the chain is empty and it reuses each name.

    The `init` statements are inline, so the output scope is `insertAllCtx ctx toInit`, which is *larger* than the
    input scope. A key of the output scope is a key of the input scope or one of the new names, which
    `insertAllCtx_keys_subset` says, and those new names are exactly the names that the group defines. Both
    branches that give the empty generator, which are an empty context of the callable procedures and a guard
    that fails, hold with no content. -/
theorem genCallStmt_mutableVars
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genCallStmt (G := SPMF) octx tvars immutableVars procs C ctx n pctx)) :
    (∀ v ∈ Block.modifiedVars (P := Expression) r.stmts,
      v ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) r.stmts false) ∧
    (∀ k ∈ Map.keys (r.outCtx.writable immutableVars),
      k ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) r.stmts false) := by
  revert r; show IsSoundFor _ _
  rw [IsSoundFor.iff_obs, genCallStmt.eq_def]
  walk [(true_law (List.mapM _ _)).obs,
    (true_law (genLExpr _ _ _ _ _ _ _)).obs,
    (true_law (elements [true, false] _)).obs]
  -- Name the instantiated in-out block `Mσ` and the chosen out targets `T`.
  all_goals
    rename_i s _ σvals _ hcond _ _ _ _ _ x hx
    generalize hMσ : StrataGenerators.Stmt.substSig (s.typeArgs.zip σvals) s.M = Mσ at hcond hx ⊢
    generalize hT : outTargets immutableVars ctx _ (functionNames C) = T at hcond hx ⊢
    simp only [callGroup_modifiedVars, callGroup_definedVars, filter_needsInit_append] at hx ⊢
  · -- Each LHS name is either `init`-defined (absent from `ctx`) or reused
    -- (bound in `ctx`, hence a mutable key, which is the writability part of `reusable`).
    rw [show s.M.keys = Mσ.keys by rw [← hMσ, StrataGenerators.Stmt.substSig_keys]] at hx
    obtain ⟨q, hq, rfl⟩ := mem_keys_append_exists Mσ T _ hx
    rcases hfind_q : ctx.find? q.1 with _ | τ
    · have hinit : needsInit ctx q = true := by simp [needsInit, VarCtx.isFresh, hfind_q]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, hinit⟩, rfl⟩)
    · -- Every out target is usable (`outTargets_all_usableName`), so the guard extends to `Mσ ++ T`.
      have hall : (List.append Mσ T).all (usableName immutableVars ctx) = true :=
        hT ▸ all_usableName_append immutableVars ctx Mσ _ _ hcond.1
      have hnotinit : needsInit ctx q = false := by simp [needsInit, VarCtx.isFresh, hfind_q]
      have hq' := List.all_eq_true.mp hall q hq
      simp only [usableName, hnotinit, Bool.or_false, reusable, hfind_q, Bool.and_eq_true,
        beq_iff_eq] at hq'
      exact List.mem_append_left _
        ((mem_writable_keys_iff ctx immutableVars q.1).mpr ⟨Map.find?_mem_keys ctx hfind_q, hq'.2⟩)
  · -- `insertAllCtx` only adds the `init`ed names, which are exactly the group's `definedVars`.
    obtain ⟨hk_keys, hk_ro⟩ := (mem_writable_keys_iff _ _ _).mp hx
    rcases List.mem_append.mp (StrataGenerators.Stmt.insertAllCtx_keys_subset _ ctx hk_keys) with h | h
    · exact List.mem_append_left _ ((mem_writable_keys_iff ctx immutableVars _).mpr ⟨h, hk_ro⟩)
    · exact List.mem_append_right _ h

-- ── The statement-level invariant (mutual over genStmt / genStmtChain) ────────

mutual

/-- **Per-statement modification-rights invariant.** Every variable a generated
    statement modifies is a key of the threaded input context or is defined by the
    statement; and every output-context key is likewise accounted for.

    Leaves: `cmd` reduces to `genCmd_mutableVars`; `exit`/`typeDecl`
    modify and define nothing (and leave `ctx` unchanged). Nesting constructors
    (`block`, `ite`, `loop`) have output scope `= ctx` and delegate both
    `modifiedVars` and `definedVars _ false` to the recursively-generated body, so
    they follow from `genStmtChain_mutableVars` at the smaller `size`. -/
theorem genStmt_mutableVars
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SPMF.support
      (genStmt (G := SPMF) octx tvars immutableVars procs labels C ctx pctx n)) :
    (∀ v ∈ Block.modifiedVars (P := Expression) r.stmts,
      v ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) r.stmts false) ∧
    (∀ k ∈ Map.keys (r.outCtx.writable immutableVars),
      k ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) r.stmts false) := by
  revert r; show IsSoundFor _ _
  cases n <;> rw [IsSoundFor.iff_obs, genStmt] <;>
  walk [fun ctx d kt => IsSoundFor.obs
          (genCmd_mutableVars octx pctx tvars immutableVars ctx d (avoid := []) (kt := kt)),
        fun d => IsSoundFor.obs (genCallStmt_mutableVars octx pctx tvars immutableVars procs C ctx d),
        fun l C ctx len => IsSoundFor.obs
          (genStmtChain_mutableVars octx pctx tvars immutableVars procs l C ctx _ len),
        (true_law (genTypeConstructor _)).obs,
        (true_law (genFreshLabel _)).obs,
        (true_law (genLExpr _ _ _ _ _ _ _)).obs,
        (true_law (genCondOrNondet _ _ _ _ _)).obs,
        (true_law (genOptMeasure _ _ _ _ _)).obs,
        (true_law (genInvariants _ _ _ _ _)).obs]
  all_goals (try simp only [block_modifiedVars_singleton, block_definedVars_singleton,
    HasVarsImp.modifiedVars, HasVarsImp.definedVars, Stmt.modifiedVars, Stmt.definedVars,
    CmdExt.modifiedVars, CmdExt.definedVars, ite_false, Bool.false_eq_true, List.not_mem_nil] at *)
    <;> grind
termination_by (n, 0, 0)

/-- **Per-sequence modification-rights invariant.** Every variable a generated
    statement *sequence* modifies is accounted for by the threaded input context's
    keys or the sequence's defined variables; and every output-context key is
    likewise accounted for.

    The `cons` case types the head via `genStmt_mutableVars`, then chains the tail
    through `trans_step`: the tail is threaded from the head's *output* context,
    whose every key `genStmt_mutableVars` already justified against
    `ctx.keys ++ definedVars head`. -/
theorem genStmtChain_mutableVars
    (octx : OpCtx) (pctx : PolyOpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (size len : Nat)
    (result : List Statement × LContext CoreLParams × VarCtx)
    (hr : result ∈ SPMF.support
      (genStmtChain (G := SPMF) octx tvars immutableVars procs labels C ctx pctx size len)) :
    (∀ v ∈ Block.modifiedVars (P := Expression) result.1,
      v ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) result.1 false) ∧
    (∀ k ∈ Map.keys (result.2.2.writable immutableVars),
      k ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) result.1 false) := by
  revert result; show IsSoundFor _ _
  cases len <;> rw [IsSoundFor.iff_obs, genStmtChain] <;>
  walk [fun C ctx => IsSoundFor.obs (genStmt_mutableVars octx pctx tvars immutableVars procs labels C ctx size),
        fun C ctx => IsSoundFor.obs (genStmtChain_mutableVars octx pctx tvars immutableVars procs labels C ctx size _)]
  all_goals (try simp only [Block.modifiedVars, block_modifiedVars_append, block_definedVars_append,
    List.not_mem_nil] at *) <;> grind
termination_by (size, 1, len)

end

end StrataGenerators.Procedure
