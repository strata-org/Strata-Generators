import StrataGenerators.StmtHasTypeAGen
import StrataGenerators.CmdHasTypeAGenSound
import Strata.Languages.Core.Procedure

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen
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

- The only command that *modifies* a variable is `set`, whose target is drawn
  from the *mutable* sub-context `ctx.writable immutableVars` via `elements` — so it
  always lands in `(ctx.writable immutableVars).keys`. Immutable names (a procedure's
  inputs) are therefore never modified.
- The only command that *grows* the context is `init`, which both defines the
  new name (`definedVars = [name]`) and adds it as a mutable key.
- The nesting statements (`block`, `ite`, `loop`) are lexically scoped: their
  output `VarCtx` is the *input* `ctx` (the body's threaded scope is discarded),
  and both `modifiedVars` and `definedVars _ false` descend into the body
  identically. So a `set` can never target a variable living only inside a
  sibling's nested block — the invariant is preserved by the recursive body.
- `genCmd` never emits `.call`; the only `.call`s come from `genCallStmt`, whose
  group writes to the callee's in-out names and out targets. Each of those is
  either reused from `ctx` (and writable, by the `usable` guard) or declared by
  the group's own inline `init` chain — so it lands in `ctx.keys ++ definedVars`
  either way. This is also the one branch whose output scope is *larger* than its
  input (`insertAllCtx ctx toInit`, the `init`s being inline rather than blocked),
  and the names it adds are exactly its `definedVars`.

Because the modified/tracked keys are those of the *mutable* sub-context, the
top-level instantiation (`ctx := inputs ++ outputs`, `immutableVars := inputs.keys`)
collapses to `outputs.keys` — exactly the `ProcHasType'.modRights` obligation —
without the inputs leaking in (they are filtered out by `writable`).

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
  simp only [VarCtx.writable, Map.keys_eq_map_fst, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp_mem, hp_pred⟩, rfl⟩
    exact ⟨⟨p, hp_mem, rfl⟩, hp_pred⟩
  · rintro ⟨⟨p, hp_mem, rfl⟩, hpred⟩
    exact ⟨p, ⟨hp_mem, hpred⟩, rfl⟩

/-- **Per-command modification-rights invariant.** For any command in `genCmd`'s
    support, every modified variable is a *mutable* key of the input context
    (all modified variables come from `set`, whose target is drawn from
    `elements (ctx.writable immutableVars)`), and every mutable output-context key is
    either a mutable input key or the freshly-`init`-defined name. -/
theorem genCmd_mutableVars
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genCmd (G := SetGen.Set) octx tvars immutableVars ctx depth)) :
    (∀ v ∈ HasVarsImp.modifiedVars (P := Expression) r.cmd,
      v ∈ Map.keys (ctx.writable immutableVars) ++ HasVarsImp.definedVars (P := Expression) r.cmd false) ∧
    (∀ k ∈ Map.keys (r.outCtx.writable immutableVars),
      k ∈ Map.keys (ctx.writable immutableVars) ++ HasVarsImp.definedVars (P := Expression) r.cmd false) := by
  rw [genCmd_support_iff] at hr
  rcases hr with hr | (hr | (⟨hlen, hr⟩ | (⟨hlen, hr⟩ | (hr | (hr | hr)))))
  · -- init_det: modified [], defined [name], outCtx = ctx.insert
    simp only [genInitDet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, _, mty, _, e, _, rfl⟩ := hr
    refine ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Cmd.modifiedVars, List.not_mem_nil] at hv, ?_⟩
    intro k hk
    rw [mem_writable_keys_iff] at hk
    obtain ⟨hk_keys, hk_ro⟩ := hk
    have hkk : k ∈ (⟨name,()⟩ : Identifier Unit) :: Map.keys ctx := Map.insert_keys ctx hk_keys
    simp only [HasVarsImp.definedVars, Cmd.definedVars]
    rcases List.mem_cons.mp hkk with rfl | h
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_left _ (mem_writable_keys_iff ctx immutableVars k |>.mpr ⟨h, hk_ro⟩)
  · -- init_nondet
    simp only [genInitNondet, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨name, _, mty, _, rfl⟩ := hr
    refine ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Cmd.modifiedVars, List.not_mem_nil] at hv, ?_⟩
    intro k hk
    rw [mem_writable_keys_iff] at hk
    obtain ⟨hk_keys, hk_ro⟩ := hk
    have hkk : k ∈ (⟨name,()⟩ : Identifier Unit) :: Map.keys ctx := Map.insert_keys ctx hk_keys
    simp only [HasVarsImp.definedVars, Cmd.definedVars]
    rcases List.mem_cons.mp hkk with rfl | h
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_left _ (mem_writable_keys_iff ctx immutableVars k |>.mpr ⟨h, hk_ro⟩)
  · -- set_det: modified [name], defined [], outCtx = ctx; name drawn from mutable
    simp only [genSetDet, VarCtx.writable, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, e, he, rfl⟩ := hr
    refine ⟨?_, fun k hk => List.mem_append_left _ hk⟩
    intro v hv
    simp only [HasVarsImp.modifiedVars, Cmd.modifiedVars, List.mem_singleton] at hv
    rw [hv]; apply List.mem_append_left
    show name ∈ Map.keys (ctx.writable immutableVars)
    rw [VarCtx.writable, Map.keys_eq_map_fst]
    exact List.mem_map.mpr ⟨(name, mty), hmem, rfl⟩
  · -- set_nondet
    simp only [genSetNondet, VarCtx.writable, mem_support_bind_iff, mem_support_pure_iff,
               mem_support_elements_iff] at hr
    obtain ⟨⟨name, mty⟩, hmem, rfl⟩ := hr
    refine ⟨?_, fun k hk => List.mem_append_left _ hk⟩
    intro v hv
    simp only [HasVarsImp.modifiedVars, Cmd.modifiedVars, List.mem_singleton] at hv
    rw [hv]; apply List.mem_append_left
    show name ∈ Map.keys (ctx.writable immutableVars)
    rw [VarCtx.writable, Map.keys_eq_map_fst]
    exact List.mem_map.mpr ⟨(name, mty), hmem, rfl⟩
  · -- assert (label sampled via `String.arbitrary`)
    simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr
    exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Cmd.modifiedVars, List.not_mem_nil] at hv,
           fun k hk => List.mem_append_left _ hk⟩
  · -- assume
    simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr
    exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Cmd.modifiedVars, List.not_mem_nil] at hv,
           fun k hk => List.mem_append_left _ hk⟩
  · -- cover
    simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, _, _, rfl⟩ := hr
    exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Cmd.modifiedVars, List.not_mem_nil] at hv,
           fun k hk => List.mem_append_left _ hk⟩

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
re-deriving each structural fact (append-distribution, behaviour on a `map`ped
list, …) by its own induction, we prove the `flatMap` characterisation **once**
below and then obtain every such fact from the standard library
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

/-- The `init … nondet` chain modifies nothing (every statement is an `init`, and
    an `init` modifies nothing — so the `flatMap` is constantly empty). -/
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
    Stmt.definedVars, HasVarsImp.definedVars, Command.definedVars, Cmd.definedVars]
  exact (List.map_eq_flatMap ..).symm

/-- The generated procedure-call *group* — the inline `init` chain followed by the
    `call`, as a statement **list** — modifies exactly the in-out names plus the
    chosen out targets, regardless of which of them were `init`ed: the `initChain`
    prefix modifies nothing, and the `call` modifies its LHS
    (`getLhs_mkArgs = M.keys ++ T.keys`). -/
theorem callGroup_modifiedVars (M T : @LMonoTySignature Unit) (pname : String)
    (missing : List (Identifier Unit × LMonoTy))
    (exprs : List Expression.Expr) :
    Block.modifiedVars (P := Expression)
      (StrataGenerators.Stmt.initChain missing ++
        [Statement.call pname (StrataGenerators.Stmt.mkArgs M T exprs) default])
      = M.keys ++ T.keys := by
  rw [block_modifiedVars_append, initChain_modifiedVars]
  simp only [List.nil_append, Block.modifiedVars, Stmt.modifiedVars, HasVarsImp.modifiedVars,
    Command.modifiedVars, StrataGenerators.Stmt.getLhs_mkArgs, List.append_nil]

/-- The generated procedure-call group defines exactly the `init`ed names
    (`missing.map Prod.fst`): the `initChain` prefix `init`s each of them; the
    `call` defines nothing. Unlike the old blocked shape there is no `block` to
    hide them — these names escape into the ambient scope, which is precisely why
    the group's output scope is `insertAllCtx ctx missing` rather than `ctx`. -/
theorem callGroup_definedVars (M T : @LMonoTySignature Unit) (pname : String)
    (missing : List (Identifier Unit × LMonoTy))
    (exprs : List Expression.Expr) :
    Block.definedVars (P := Expression)
      (StrataGenerators.Stmt.initChain missing ++
        [Statement.call pname (StrataGenerators.Stmt.mkArgs M T exprs) default]) false
      = missing.map Prod.fst := by
  rw [block_definedVars_append, initChain_definedVars]
  simp only [Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars, Command.definedVars,
    List.append_nil]

/-- A required name `v ∈ M.keys ++ T.keys` is a key of `M ++ T`, the variables the
    call writes to.
    Bridges from the `getLhs_mkArgs` write-set (`M.keys ++ T.keys`) back to the
    in-out block and out targets the generator reasons about. -/
theorem mem_keys_append_exists (M T : @LMonoTySignature Unit) (v : Identifier Unit)
    (hv : v ∈ M.keys ++ T.keys) :
    ∃ q : Identifier Unit × LMonoTy, q ∈ List.append M T ∧ q.1 = v := by
  -- `keys` is `map Prod.fst`, so the two appended key-lists are one `map` of the
  -- appended signature — then this is just `List.mem_map`.
  rw [ListMap.keys_eq_map_fst, ListMap.keys_eq_map_fst, ← List.map_append] at hv
  exact List.mem_map.mp hv

/-- **Per-call-statement modification-rights invariant.** The emitted group is the
    inline `init` chain followed by the `call` (a statement *list*, spliced into the
    ambient scope — there is no enclosing `block`). Every modified variable — the
    call's LHS `M.keys ++ T.keys` — is accounted for by the *mutable* input keys
    plus the group's defined names:

    * a *reused* name is bound in `ctx` **and** not immutable (the `usable` guard —
      which, for an out target, is `outTargets_all_usableName`), hence a key of
      `ctx.writable immutableVars`;
    * an *absent* name — a fresh in-out name, or an *invented* out target — is
      `init`-defined by the inline chain (`definedVars = toInit.map Prod.fst`).
      When nothing needs `init`ing the chain is empty and every name is reused.

    Because the `init`s are inline, the output scope is `insertAllCtx ctx toInit`,
    genuinely *larger* than `ctx`: an output key is either an input key or one of
    the freshly-declared names, and `insertAllCtx_keys_subset` says exactly that —
    the declared names being precisely the group's `definedVars`. Both
    empty-generator branches (empty `procs`, guard false) discharge vacuously. -/
theorem genCallStmt_mutableVars
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genCallStmt (G := SetGen.Set) octx tvars immutableVars procs C ctx n)) :
    (∀ v ∈ Block.modifiedVars (P := Expression) r.stmts,
      v ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) r.stmts false) ∧
    (∀ k ∈ Map.keys (r.outCtx.writable immutableVars),
      k ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) r.stmts false) := by
  cases procs with
  | nil => simp only [genCallStmt, SetGen.support, SetGen.bot_mem_iff] at hr
  | cons p₀ ps =>
    simp only [genCallStmt, mem_support_bind_iff, mem_support_elements_iff] at hr
    obtain ⟨s, hs, hr⟩ := hr
    -- Peel the type-instantiation sampling; name the instantiated blocks.
    obtain ⟨σvals, _, hr⟩ := hr
    obtain ⟨σ, hσ⟩ : ∃ σ, s.typeArgs.zip σvals = σ := ⟨_, rfl⟩
    obtain ⟨Mσ, hMσ⟩ : ∃ Mσ, StrataGenerators.Stmt.substSig σ s.M = Mσ := ⟨_, rfl⟩
    obtain ⟨Oσ, hOσ⟩ : ∃ Oσ, StrataGenerators.Stmt.substSig σ s.O = Oσ := ⟨_, rfl⟩
    simp only [hσ, hMσ, hOσ] at hr
    split at hr
    · rename_i hcond
      obtain ⟨hMusable, _hNodup⟩ := hcond
      -- Name the generator's chosen out targets; every one of them is usable
      -- (`outTargets_all_usableName`), so the guard over `Mσ` extends to `Mσ ++ T`.
      obtain ⟨T, hT⟩ : ∃ T, outTargets immutableVars ctx Oσ = T := ⟨_, rfl⟩
      have hallusable : (List.append Mσ T).all (usableName immutableVars ctx) = true := by
        rw [← hT]; exact all_usableName_append immutableVars ctx Mσ Oσ hMusable
      rw [hT] at hr
      simp only [mem_support_bind_iff] at hr
      obtain ⟨exprs, hexprs, hr⟩ := hr
      -- A reused name (bound in `ctx`, hence `reusable` rather than `needsInit`) is
      -- a mutable key of `ctx` — that is exactly `reusable`'s writability bit.
      have hReuseWritable : ∀ q ∈ List.append Mσ T, ∀ τ,
          ctx.find? q.1 = some τ → q.1 ∈ Map.keys (ctx.writable immutableVars) := by
        intro q hq τ hfind_q
        have hq' := List.all_eq_true.mp hallusable q hq
        have hnotinit : needsInit ctx q = false := by
          simp [needsInit, VarCtx.isFresh, hfind_q]
        have hreuse : reusable immutableVars ctx q = true := by
          simp only [usableName, hnotinit, Bool.or_false] at hq'; exact hq'
        simp only [reusable, hfind_q, Bool.and_eq_true, beq_iff_eq] at hreuse
        exact (mem_writable_keys_iff ctx immutableVars q.1).mpr
          ⟨Map.find?_mem_keys ctx hfind_q, hreuse.2⟩
      -- One uniform shape now: `initChain toInit ++ [call]`, with no `isEmpty`
      -- split (when nothing needs `init`ing the chain is simply `[]`).
      simp only [mem_support_pure_iff] at hr
      obtain rfl := hr
      -- Fuse the recipe's in-out-then-out-target init lists into the single filter
      -- over `Mσ ++ T`, which is the form both `definedVars` and `insertAllCtx`
      -- are stated at below.
      rw [callGroup_modifiedVars, callGroup_definedVars, filter_needsInit_append]
      -- `substSig` preserves keys, so the call's LHS names (from `mkArgs s.M …`) are
      -- the same names as the instantiated write-list `Mσ`'s keys.
      have hMkeys : s.M.keys = Mσ.keys := by rw [← hMσ, StrataGenerators.Stmt.substSig_keys]
      refine ⟨fun v hv => ?_, fun k hk => ?_⟩
      · -- Each LHS name is either `init`-defined (absent from `ctx`) or reused
        -- (bound in `ctx`, hence a mutable key).
        rw [hMkeys] at hv
        obtain ⟨q, hq, rfl⟩ := mem_keys_append_exists Mσ T v hv
        rcases hfind_q : ctx.find? q.1 with _ | τ
        · -- absent ⇒ fresh ⇒ `needsInit`, so `q` is in the init list.
          apply List.mem_append_right
          refine List.mem_map.mpr ⟨q, ?_, rfl⟩
          exact List.mem_filter.mpr ⟨hq, by simp [needsInit, VarCtx.isFresh, hfind_q]⟩
        · exact List.mem_append_left _ (hReuseWritable q hq τ hfind_q)
      · -- The output scope is genuinely larger than `ctx`: `insertAllCtx` only adds
        -- the `init`ed names, which are exactly the group's `definedVars`.
        rw [mem_writable_keys_iff] at hk
        obtain ⟨hk_keys, hk_ro⟩ := hk
        rcases List.mem_append.mp
            (StrataGenerators.Stmt.insertAllCtx_keys_subset _ ctx hk_keys) with h | h
        · exact List.mem_append_left _
            ((mem_writable_keys_iff ctx immutableVars k).mpr ⟨h, hk_ro⟩)
        · exact List.mem_append_right _ h
    · simp only [SetGen.support, SetGen.bot_mem_iff] at hr

-- ── The statement-level invariant (mutual over genStmt / genStmtChain) ────────

mutual

/-- **Per-statement modification-rights invariant.** Every variable a generated
    statement modifies is a key of the threaded input context or is defined by the
    statement; and every output-context key is likewise accounted for.

    Leaves: `cmd` reduces to `genCmd_mutableVars`; `exit`/`funcDecl`/`typeDecl`
    modify and define nothing (and leave `ctx` unchanged). Nesting constructors
    (`block`, `ite`, `loop`) have output scope `= ctx` and delegate both
    `modifiedVars` and `definedVars _ false` to the recursively-generated body, so
    they follow from `genStmtChain_mutableVars` at the smaller `size`. -/
theorem genStmt_mutableVars
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genStmt (G := SetGen.Set) octx tvars immutableVars procs labels C ctx n)) :
    (∀ v ∈ Block.modifiedVars (P := Expression) r.stmts,
      v ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) r.stmts false) ∧
    (∀ k ∈ Map.keys (r.outCtx.writable immutableVars),
      k ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) r.stmts false) := by
  cases n with
  | zero =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · -- cmd
      simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨rc, hrc, rfl⟩ := hr
      have h := genCmd_mutableVars octx tvars immutableVars ctx 0 rc hrc
      simpa only [block_modifiedVars_singleton, block_definedVars_singleton,
        HasVarsImp.modifiedVars, HasVarsImp.definedVars, Stmt.modifiedVars,
        Stmt.definedVars, Command.modifiedVars, Command.definedVars] using h
    · -- exit
      cases labels with
      | nil => simp only [genExitStmt, SetGen.support, SetGen.bot_mem_iff] at hr
      | cons hd tl =>
        simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff, mem_support_elements_iff] at hr
        obtain ⟨_, _, rfl⟩ := hr
        exact ⟨fun v hv => by
                 simp only [block_modifiedVars_singleton, Stmt.modifiedVars,
                   List.not_mem_nil] at hv,
               fun k hk => List.mem_append_left _ hk⟩
    · -- funcDecl
      simp only [genFuncDeclStmt, genDecl, mem_support_bind_iff, mem_support_map_iff, mem_support_pure_iff] at hr
      obtain ⟨_, _, _, _, rfl⟩ := hr
      exact ⟨fun v hv => by
               simp only [block_modifiedVars_singleton, Stmt.modifiedVars,
                 List.not_mem_nil] at hv,
             fun k hk => List.mem_append_left _ hk⟩
    · -- typeDecl
      simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
      obtain ⟨tc, _, hr⟩ := hr
      split at hr
      · simp only [mem_support_pure_iff] at hr; subst hr
        exact ⟨fun v hv => by
                 simp only [block_modifiedVars_singleton, Stmt.modifiedVars,
                   List.not_mem_nil] at hv,
               fun k hk => List.mem_append_left _ hk⟩
      · simp only [SetGen.support, SetGen.bot_mem_iff] at hr
    · -- call
      exact genCallStmt_mutableVars octx tvars immutableVars procs C ctx 0 _ hr
  | succ size =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · -- cmd
      simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨rc, hrc, rfl⟩ := hr
      have h := genCmd_mutableVars octx tvars immutableVars ctx (size+1) rc hrc
      simpa only [block_modifiedVars_singleton, block_definedVars_singleton,
        HasVarsImp.modifiedVars, HasVarsImp.definedVars, Stmt.modifiedVars,
        Stmt.definedVars, Command.modifiedVars, Command.definedVars] using h
    · -- exit
      cases labels with
      | nil => simp only [genExitStmt, SetGen.support, SetGen.bot_mem_iff] at hr
      | cons hd tl =>
        simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff, mem_support_elements_iff] at hr
        obtain ⟨_, _, rfl⟩ := hr
        exact ⟨fun v hv => by
                 simp only [block_modifiedVars_singleton, Stmt.modifiedVars,
                   List.not_mem_nil] at hv,
               fun k hk => List.mem_append_left _ hk⟩
    · -- funcDecl
      simp only [genFuncDeclStmt, genDecl, mem_support_bind_iff, mem_support_map_iff, mem_support_pure_iff] at hr
      obtain ⟨_, _, _, _, rfl⟩ := hr
      exact ⟨fun v hv => by
               simp only [block_modifiedVars_singleton, Stmt.modifiedVars,
                 List.not_mem_nil] at hv,
             fun k hk => List.mem_append_left _ hk⟩
    · -- typeDecl
      simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
      obtain ⟨tc, _, hr⟩ := hr
      split at hr
      · simp only [mem_support_pure_iff] at hr; subst hr
        exact ⟨fun v hv => by
                 simp only [block_modifiedVars_singleton, Stmt.modifiedVars,
                   List.not_mem_nil] at hv,
               fun k hk => List.mem_append_left _ hk⟩
      · simp only [SetGen.support, SetGen.bot_mem_iff] at hr
    · -- call
      exact genCallStmt_mutableVars octx tvars immutableVars procs C ctx (size+1) _ hr
    · -- block: outCtx = ctx, modified/defined delegate to body
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨label, hlabel, ⟨⟨len, _⟩⟩, _, triple, htriple, rfl⟩ := hr
      have ih := genStmtChain_mutableVars octx tvars immutableVars procs (label :: labels) C ctx size len triple htriple
      simp only [block_modifiedVars_singleton, block_definedVars_singleton,
        Stmt.modifiedVars, Stmt.definedVars, if_false, Bool.false_eq_true]
      refine ⟨ih.1, fun k hk => List.mem_append_left _ hk⟩
    · -- ite_det
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨cond, hcond, ⟨⟨tlen, _⟩⟩, _, ⟨⟨elen, _⟩⟩, _, tt, htt, et, het, rfl⟩ := hr
      have iht := genStmtChain_mutableVars octx tvars immutableVars procs labels C ctx size tlen tt htt
      have ihe := genStmtChain_mutableVars octx tvars immutableVars procs labels C ctx size elen et het
      simp only [block_modifiedVars_singleton, block_definedVars_singleton,
        Stmt.modifiedVars, Stmt.definedVars, if_false, Bool.false_eq_true]
      refine ⟨ite_combine _ _ _ _ _ iht.1 ihe.1, fun k hk => List.mem_append_left _ hk⟩
    · -- ite_nondet
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨⟨⟨tlen, _⟩⟩, _, ⟨⟨elen, _⟩⟩, _, tt, htt, et, het, rfl⟩ := hr
      have iht := genStmtChain_mutableVars octx tvars immutableVars procs labels C ctx size tlen tt htt
      have ihe := genStmtChain_mutableVars octx tvars immutableVars procs labels C ctx size elen et het
      simp only [block_modifiedVars_singleton, block_definedVars_singleton,
        Stmt.modifiedVars, Stmt.definedVars, if_false, Bool.false_eq_true]
      refine ⟨ite_combine _ _ _ _ _ iht.1 ihe.1, fun k hk => List.mem_append_left _ hk⟩
    · -- loop
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨guard, hguard, measure, hmeasure, invs, hinvs, ⟨⟨blen, _⟩⟩, _, body, hbody, rfl⟩ := hr
      have ih := genStmtChain_mutableVars octx tvars immutableVars procs labels C ctx size blen body hbody
      simp only [block_modifiedVars_singleton, block_definedVars_singleton,
        Stmt.modifiedVars, Stmt.definedVars, if_false, Bool.false_eq_true]
      refine ⟨ih.1, fun k hk => List.mem_append_left _ hk⟩
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
    (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (procs : ProcSigCtx)
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (size len : Nat)
    (result : List Statement × LContext CoreLParams × VarCtx)
    (hr : result ∈ SetGen.support (genStmtChain (G := SetGen.Set) octx tvars immutableVars procs labels C ctx size len)) :
    (∀ v ∈ Block.modifiedVars (P := Expression) result.1,
      v ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) result.1 false) ∧
    (∀ k ∈ Map.keys (result.2.2.writable immutableVars),
      k ∈ Map.keys (ctx.writable immutableVars) ++ Block.definedVars (P := Expression) result.1 false) := by
  cases len with
  | zero =>
    simp only [genStmtChain, mem_support_pure_iff] at hr
    subst hr
    refine ⟨fun v hv => ?_, fun k hk => ?_⟩
    · simp only [Block.modifiedVars, List.not_mem_nil] at hv
    · exact List.mem_append_left _ hk
  | succ len =>
    simp only [genStmtChain, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨rhead, hhead, rtail, htail, rfl⟩ := hr
    have hh := genStmt_mutableVars octx tvars immutableVars procs labels C ctx size rhead hhead
    have ht := genStmtChain_mutableVars octx tvars immutableVars procs labels rhead.outC rhead.outCtx size len rtail htail
    -- The head is a statement *list* now, so the chain **appends** it rather than
    -- consing: both write-sets split by `block_*_append`, not by the cons equations.
    rw [block_modifiedVars_append, block_definedVars_append]
    obtain ⟨hh_mod, hh_key⟩ := hh
    obtain ⟨ht_mod, ht_key⟩ := ht
    refine ⟨fun v hv => ?_, fun k hk => ?_⟩
    · rcases List.mem_append.mp hv with h | h
      · exact mem_append_grow_r v _ _ _ (hh_mod v h)
      · exact trans_step v _ _ _ _ hh_key (ht_mod v h)
    · exact trans_step k _ _ _ _ hh_key (ht_key k hk)
termination_by (size, 1, len)

end

end StrataGenerators.Procedure
