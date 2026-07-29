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

`genProcedure` builds its body via `genStmts`, seeding the threaded `VarCtx` with
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
- `genCmd` never emits `.call`, the only other source of `modifiedVars`.

Because the modified/tracked keys are those of the *mutable* sub-context, the
top-level instantiation (`ctx := inputs ++ outputs`, `immutableVars := inputs.keys`)
collapses to `outputs.keys` — exactly the `ProcHasType'.modRights` obligation —
without the inputs leaking in (they are filtered out by `writable`).
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
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit)) (ctx : VarCtx) (depth : Nat)
    (r : GenCmdResult)
    (hr : r ∈ SetGen.support (genCmd (G := SetGen.Set) fctx octx tvars immutableVars ctx depth)) :
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
  · -- assert
    simp only [genAssertCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr
    exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Cmd.modifiedVars, List.not_mem_nil] at hv,
           fun k hk => List.mem_append_left _ hk⟩
  · -- assume
    simp only [genAssumeCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr
    exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Cmd.modifiedVars, List.not_mem_nil] at hv,
           fun k hk => List.mem_append_left _ hk⟩
  · -- cover
    simp only [genCoverCmd, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr
    exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Cmd.modifiedVars, List.not_mem_nil] at hv,
           fun k hk => List.mem_append_left _ hk⟩

-- ── Membership-monotonicity helpers ──────────────────────────────────────

/-- Grow the *defined-set* summand on the right of an `xs ++ ys` membership. -/
theorem mem_append_grow_r {α} (v : α) (xs ys zs : List α)
    (h : v ∈ xs ++ ys) : v ∈ xs ++ (ys ++ zs) := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_append_left _ h)

/-- Insert a middle summand into an `xs ++ zs` membership. -/
theorem mem_append_grow_mid {α} (v : α) (xs ys zs : List α)
    (h : v ∈ xs ++ zs) : v ∈ xs ++ (ys ++ zs) := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_append_right _ h)

/-- Chain a threaded modified/key fact through a sequence step: something
    accounted for by the *tail's* context `B ++ defT`, where every element of `B`
    is itself accounted for by `xs ++ defH`, is accounted for by
    `xs ++ (defH ++ defT)`. -/
theorem trans_step {α} (x : α) (B xs defH defT : List α)
    (hB : ∀ y ∈ B, y ∈ xs ++ defH)
    (hx : x ∈ B ++ defT) : x ∈ xs ++ (defH ++ defT) := by
  rcases List.mem_append.mp hx with h | h
  · exact mem_append_grow_r x xs defH defT (hB x h)
  · exact List.mem_append_right _ (List.mem_append_right _ h)

/-- Combine the two branches of an `ite` (whose output scope is the input `ctx`):
    the concatenated modified-set is justified by the concatenated defined-set.
    Stated over an arbitrary key list `keys` (instantiated at
    `Map.keys (ctx.writable immutableVars)`). -/
theorem ite_combine (keys : List Expression.Ident)
    (modT modE defT defE : List Expression.Ident)
    (hT : ∀ v ∈ modT, v ∈ keys ++ defT)
    (hE : ∀ v ∈ modE, v ∈ keys ++ defE) :
    (∀ v ∈ modT ++ modE, v ∈ keys ++ (defT ++ defE)) := by
  intro v hv
  rcases List.mem_append.mp hv with h | h
  · exact mem_append_grow_r v _ _ _ (hT v h)
  · exact mem_append_grow_mid v _ _ _ (hE v h)

-- ── The statement-level invariant (mutual over genStmt / genStmts) ────────

mutual

/-- **Per-statement modification-rights invariant.** Every variable a generated
    statement modifies is a key of the threaded input context or is defined by the
    statement; and every output-context key is likewise accounted for.

    Leaves: `cmd` reduces to `genCmd_mutableVars`; `exit`/`funcDecl`/`typeDecl`
    modify and define nothing (and leave `ctx` unchanged). Nesting constructors
    (`block`, `ite`, `loop`) have output scope `= ctx` and delegate both
    `modifiedVars` and `definedVars _ false` to the recursively-generated body, so
    they follow from `genStmts_mutableVars` at the smaller `size`. -/
theorem genStmt_mutableVars
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (n : Nat)
    (r : GenStmtResult)
    (hr : r ∈ SetGen.support (genStmt (G := SetGen.Set) fctx octx tvars immutableVars labels C ctx n)) :
    (∀ v ∈ HasVarsImp.modifiedVars (P := Expression) r.stmt,
      v ∈ Map.keys (ctx.writable immutableVars) ++ HasVarsImp.definedVars (P := Expression) r.stmt false) ∧
    (∀ k ∈ Map.keys (r.outCtx.writable immutableVars),
      k ∈ Map.keys (ctx.writable immutableVars) ++ HasVarsImp.definedVars (P := Expression) r.stmt false) := by
  cases n with
  | zero =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · -- cmd
      simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨rc, hrc, rfl⟩ := hr
      have h := genCmd_mutableVars fctx octx tvars immutableVars ctx 0 rc hrc
      simpa only [HasVarsImp.modifiedVars, HasVarsImp.definedVars, Stmt.modifiedVars,
        Stmt.definedVars, Command.modifiedVars, Command.definedVars] using h
    · -- exit
      cases labels with
      | nil => simp only [genExitStmt, SetGen.support, SetGen.bot_mem_iff] at hr
      | cons hd tl =>
        simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff, mem_support_elements_iff] at hr
        obtain ⟨_, _, rfl⟩ := hr
        exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Stmt.modifiedVars, List.not_mem_nil] at hv,
               fun k hk => List.mem_append_left _ hk⟩
    · -- funcDecl
      simp only [genFuncDeclStmt, genDecl, mem_support_bind_iff, mem_support_map_iff, mem_support_pure_iff] at hr
      obtain ⟨_, _, _, _, rfl⟩ := hr
      exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Stmt.modifiedVars, List.not_mem_nil] at hv,
             fun k hk => List.mem_append_left _ hk⟩
    · -- typeDecl
      simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
      obtain ⟨tc, _, hr⟩ := hr
      split at hr
      · simp only [mem_support_pure_iff] at hr; subst hr
        exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Stmt.modifiedVars, List.not_mem_nil] at hv,
               fun k hk => List.mem_append_left _ hk⟩
      · simp only [SetGen.support, SetGen.bot_mem_iff] at hr
  | succ size =>
    simp only [genStmt, mem_support_frequency_iff] at hr
    obtain ⟨w, g, hg, _, hr⟩ := hr
    simp only [List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hg
    rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · -- cmd
      simp only [genCmdStmt, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨rc, hrc, rfl⟩ := hr
      have h := genCmd_mutableVars fctx octx tvars immutableVars ctx (size+1) rc hrc
      simpa only [HasVarsImp.modifiedVars, HasVarsImp.definedVars, Stmt.modifiedVars,
        Stmt.definedVars, Command.modifiedVars, Command.definedVars] using h
    · -- exit
      cases labels with
      | nil => simp only [genExitStmt, SetGen.support, SetGen.bot_mem_iff] at hr
      | cons hd tl =>
        simp only [genExitStmt, mem_support_bind_iff, mem_support_pure_iff, mem_support_elements_iff] at hr
        obtain ⟨_, _, rfl⟩ := hr
        exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Stmt.modifiedVars, List.not_mem_nil] at hv,
               fun k hk => List.mem_append_left _ hk⟩
    · -- funcDecl
      simp only [genFuncDeclStmt, genDecl, mem_support_bind_iff, mem_support_map_iff, mem_support_pure_iff] at hr
      obtain ⟨_, _, _, _, rfl⟩ := hr
      exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Stmt.modifiedVars, List.not_mem_nil] at hv,
             fun k hk => List.mem_append_left _ hk⟩
    · -- typeDecl
      simp only [genTypeDeclStmt, mem_support_bind_iff] at hr
      obtain ⟨tc, _, hr⟩ := hr
      split at hr
      · simp only [mem_support_pure_iff] at hr; subst hr
        exact ⟨fun v hv => by simp only [HasVarsImp.modifiedVars, Stmt.modifiedVars, List.not_mem_nil] at hv,
               fun k hk => List.mem_append_left _ hk⟩
      · simp only [SetGen.support, SetGen.bot_mem_iff] at hr
    · -- block: outCtx = ctx, modified/defined delegate to body
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨label, hlabel, ⟨⟨len, _⟩⟩, _, triple, htriple, rfl⟩ := hr
      have ih := genStmts_mutableVars fctx octx tvars immutableVars (label :: labels) C ctx size len triple htriple
      simp only [HasVarsImp.modifiedVars, HasVarsImp.definedVars, Stmt.modifiedVars, Stmt.definedVars,
        if_false, Bool.false_eq_true]
      refine ⟨ih.1, fun k hk => List.mem_append_left _ hk⟩
    · -- ite_det
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨cond, hcond, ⟨⟨tlen, _⟩⟩, _, ⟨⟨elen, _⟩⟩, _, tt, htt, et, het, rfl⟩ := hr
      have iht := genStmts_mutableVars fctx octx tvars immutableVars labels C ctx size tlen tt htt
      have ihe := genStmts_mutableVars fctx octx tvars immutableVars labels C ctx size elen et het
      simp only [HasVarsImp.modifiedVars, HasVarsImp.definedVars, Stmt.modifiedVars, Stmt.definedVars,
        if_false, Bool.false_eq_true]
      refine ⟨ite_combine _ _ _ _ _ iht.1 ihe.1, fun k hk => List.mem_append_left _ hk⟩
    · -- ite_nondet
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨⟨⟨tlen, _⟩⟩, _, ⟨⟨elen, _⟩⟩, _, tt, htt, et, het, rfl⟩ := hr
      have iht := genStmts_mutableVars fctx octx tvars immutableVars labels C ctx size tlen tt htt
      have ihe := genStmts_mutableVars fctx octx tvars immutableVars labels C ctx size elen et het
      simp only [HasVarsImp.modifiedVars, HasVarsImp.definedVars, Stmt.modifiedVars, Stmt.definedVars,
        if_false, Bool.false_eq_true]
      refine ⟨ite_combine _ _ _ _ _ iht.1 ihe.1, fun k hk => List.mem_append_left _ hk⟩
    · -- loop
      simp only [mem_support_bind_iff, mem_support_pure_iff, mem_support_choose_iff] at hr
      obtain ⟨guard, hguard, measure, hmeasure, invs, hinvs, ⟨⟨blen, _⟩⟩, _, body, hbody, rfl⟩ := hr
      have ih := genStmts_mutableVars fctx octx tvars immutableVars labels C ctx size blen body hbody
      simp only [HasVarsImp.modifiedVars, HasVarsImp.definedVars, Stmt.modifiedVars, Stmt.definedVars,
        if_false, Bool.false_eq_true]
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
theorem genStmts_mutableVars
    (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier)
    (immutableVars : List (Identifier Unit))
    (labels : List String)
    (C : LContext CoreLParams) (ctx : VarCtx) (size len : Nat)
    (result : List Statement × LContext CoreLParams × VarCtx)
    (hr : result ∈ SetGen.support (genStmts (G := SetGen.Set) fctx octx tvars immutableVars labels C ctx size len)) :
    (∀ v ∈ HasVarsImp.modifiedVars (P := Expression) result.1,
      v ∈ Map.keys (ctx.writable immutableVars) ++ HasVarsImp.definedVars (P := Expression) result.1 false) ∧
    (∀ k ∈ Map.keys (result.2.2.writable immutableVars),
      k ∈ Map.keys (ctx.writable immutableVars) ++ HasVarsImp.definedVars (P := Expression) result.1 false) := by
  cases len with
  | zero =>
    simp only [genStmts, mem_support_pure_iff] at hr
    subst hr
    refine ⟨fun v hv => ?_, fun k hk => ?_⟩
    · simp only [HasVarsImp.modifiedVars, Block.modifiedVars, List.not_mem_nil] at hv
    · exact List.mem_append_left _ hk
  | succ len =>
    simp only [genStmts, mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨rhead, hhead, rtail, htail, rfl⟩ := hr
    have hh := genStmt_mutableVars fctx octx tvars immutableVars labels C ctx size rhead hhead
    have ht := genStmts_mutableVars fctx octx tvars immutableVars labels rhead.outC rhead.outCtx size len rtail htail
    simp only [HasVarsImp.modifiedVars, HasVarsImp.definedVars, Block.modifiedVars, Block.definedVars]
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
