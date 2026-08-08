# Plan: generate polymorphic procedure calls (issue #28)

## Status

- **Implemented.** The generator (`genCallStmt`) now samples a concrete type
  instantiation `σ` over each callee's `typeArgs`, and the full soundness /
  mutableVars / completeness proof chain has been σ-generalized. The whole worktree
  builds (256 jobs) and the key theorems (`call_recipe_inout_sound`,
  `call_mixed_body_sound`, `genCallStmt_sound`, `genCallStmt_mem_complete`,
  `genStmt_sound`, `genProcedure_sound`, `spec_complete`) are axiom-clean
  (`[propext, Classical.choice, Quot.sound]`). Verified empirically: `genCallStmt`
  emits calls to a polymorphic callee `P0<a>(inout m:a, in i:int, out o:a)` at many
  concrete instantiations of `a`, and `test-plain` shows the same 9 pre-existing
  failures as baseline (all funcDecl / round-trip, none call-related).
- Sibling work in issue #32 (split-point `findPolymorphicOps`) was the direct
  methodological template: sample a concrete instantiation for a scheme's free type
  variables, build the argument types as that instance, and prove the emitted term
  is a genuine substitution instance.
- The notes below record the design as executed; a couple of small deviations from
  the original sketch are called out inline (search "DEVIATION").

## The current restriction (what #28 removes)

`genProcedure` already emits **polymorphic** procedures — it draws a non-empty
`typeArgs` via `genTypeArgs` and types the I/O signature over them
(`ProcedureHasTypeAGen/Core.lean`). But `genCallStmt` can only call **monomorphic**
callees:

- `ProcSigCorresponds` (`StmtHasTypeAGen/GenCallStmtSound.lean:57`) pins
  `proc.header.typeArgs = []` for every listed callee.
- The soundness kernel `call_recipe_inout_sound`
  (`GenCallStmtSound.lean:406`) hardwires the `CmdExtHasType'.call` rule's
  type-instantiation witness to `σ := []` (the identity substitution) and uses
  `LMonoTy.subst_emptyS` to erase it everywhere (lines 425–426, 471, 526).
- The harness (`TestScaffold.lean:620`, `genProcsWith`) filters generated
  procedures to feed only monomorphic (`typeArgs.isEmpty`) siblings into the
  callable `ProcSigCtx`; polymorphic siblings are silently dropped as call targets.

The Core `call` rule (`.lake/.../Core/CommandTypeSpec.lean:51`) already
existentially quantifies a type instantiation `σ`: input/LHS types are matched
against `LMonoTy.subst [σ] (proc.header.inputs.values[i])` etc. So the spec fully
supports polymorphic calls — the generator simply never exercises a non-identity
`σ`. #28 = sample a concrete `σ`, instantiate the callee's signature by it, and
thread that `σ` through the call rule instead of `[]`.

## Design

### Generator side

1. **`ProcSig` gains type parameters.** Add `typeArgs : List TyIdentifier` to
   `ProcSig` (`GenCallStmtSound.lean`). `M`/`I`/`O` continue to store the callee's
   *declared* (un-instantiated, over `typeArgs`) block types. `headerProcSig`
   (`ProcedureHasTypeAGen/Core.lean`) records `h.typeArgs` instead of discarding
   it; the harness feeds **all** siblings, not just monomorphic ones.

   A `substSig σ block := block.map (fun (x,t) => (x, subst [σ] t))` helper (with
   `substSig_keys`/`_length`/`_values`/`_append`/`_nil` and two `getElem` lemmas)
   applies an instantiation to a block on demand. `substSig_nil : substSig [] = id`
   is the bridge that makes the monomorphic path a definitional special case.

2. **`genCallStmt` samples an instantiation `σ`.** In the `p₀ :: ps` body
   (`StmtHasTypeAGen/Core.lean:379`), after picking the callee `s`:
   - draw `sampledTys` — one generable monotype per element of `s.typeArgs` — via the
     same context-driven sampling `genIndirPoly` uses (`elements generableTys`, or a
     `.bool` fallback when none are generable). Reuse
     `generableTypesFromCtx`-style logic; the analogue already exists for expressions.
   - form `σ := s.typeArgs.zip sampledTys` and the instantiated blocks
     `Mσ := s.M.map (fun (x,t) => (x, LMonoTy.subst [σ] t))`, likewise `Iσ`, `Oσ`.
   - **All downstream generator logic runs on the instantiated blocks `Mσ/Iσ/Oσ`**
     (reuse/init decisions, `outTargets`, `mkArgs`, by-value input generation at
     `Iσ.values`). The emitted `Statement.call` is unchanged in shape; only the types
     the args must inhabit are now the instantiated ones.
   - The monomorphic case is exactly `typeArgs = []` ⇒ `σ = []` ⇒ `Mσ = M`, so this
     is a strict generalization and the existing behaviour is preserved definitionally.

   Note: `σ` is a proper instantiation only over the callee's *own* `typeArgs`. The
   callee's block types may still mention the **enclosing** procedure's rigid
   `typeArgs` (those are legal ambient free type vars); `σ` must not touch them, so
   `σ`'s domain is exactly `s.typeArgs`. This mirrors `findPolymorphicOps`'s
   freshening discipline — worth freshening `s.typeArgs` away from the ambient
   `tvars`/generable-set before zipping, exactly as `freshenBoundVars` does, to avoid
   capture when a callee's type-arg name coincides with an enclosing rigid one.

### Proof side (five files)

The whole proof already flows through `σ` symbolically in the spec; the only place
`σ = []` is *assumed* is the two soundness kernels. The plan is to make the kernels
`σ`-generic and instantiate at the sampled `σ` rather than `[]`.

1. **`call_recipe_inout_sound` (`GenCallStmtSound.lean:406`).** Generalize:
   - Add a parameter `σ : List (TyIdentifier × LMonoTy)`.
   - Replace `hInputs : proc.header.inputs = M ++ I` with the *instantiated* form the
     rule needs: keep `proc.header.inputs = M₀ ++ I₀` (declared blocks) and pass the
     relation `M = M₀.map (subst [σ] ·)` etc., **or** — simpler — restate the kernel
     directly over instantiated blocks `M/I/O` plus a hypothesis that they equal
     `subst [σ]` of the declared blocks, and feed the call rule `σ` as the witness.
   - `apply CmdExtHasType'.call Γ pname (mkArgs …) proc md σ` (was `[]`).
   - The identity-erasure steps (`hsubst : subst [[]] t = t`) become: the value at
     input position `i` is `subst [σ] (proc.header.inputs.values[i])`, which — by the
     instantiation relation — is definitionally the `i`-th value of the instantiated
     block. So the `AliasEquiv.refl` witness still works with `mty` := the
     instantiated value; no `subst_emptyS`. The index/append arithmetic (steps 2–7)
     is unchanged because it is all phrased over the instantiated blocks' lengths,
     which match the declared blocks' lengths (`List.length_map`).
   - Premises 5/6 pick `mty := (Mσ.values ++ Iσ.values)[i]` and need
     `AliasEquiv Γ.aliases mty (subst [σ] declared.values[i])`; with `mty` chosen as
     the instantiated value this is `AliasEquiv.refl` again.

2. **`call_mixed_body_sound` (`:690`).** Purely a wrapper over
   `call_recipe_inout_sound` + `initChain_types` + `StmtsHasTypeA_append`. It threads
   `M/I/O/T` and the `hReuse`/`hExTy` facts. Restate its `M/I/O` as the instantiated
   blocks (the caller already passes whatever blocks the args must inhabit), add the
   `σ` parameter, forward it to `call_recipe_inout_sound`. `outTargets_inΓ`,
   `insertAll_*`, `missingIn_*` are all type-agnostic and untouched.

3. **`genCallStmt_sound` (`StmtHasTypeAGen.lean:371`).** After destructuring the
   `do`-block, additionally destructure the `sampledTys` bind (mirrors
   `genIndirPoly_sound`'s outer `mapM` peel). Recompute `Mσ/Iσ/Oσ`, `hInputs`/
   `hOutputs` become the instantiated equalities (from `hProcs`'s declared equalities
   + `subst [σ]` congruence — one `List.map` rewrite each). `hExTy` now types each
   drawn input at `Iσ.values[i]` (the generator drew it at that instantiated type, so
   `env.exprSound` gives it directly). Feed `σ` and the instantiated blocks to
   `call_mixed_body_sound`. The `hReuse` transport across `VarCtxCorresponds` is
   unchanged (it inspects `ctx`/`Γ` at the *instantiated* names, which is what the
   generator used).

4. **`ProcSigCorresponds` (`GenCallStmtSound.lean:57`).** Drop the
   `typeArgs = []` conjunct; keep the block decomposition over the *declared*
   signature (`inputs = M ++ I`, `outputs = M ++ O` with `M/I/O` the declared
   blocks). `headerProcSig` already reconstructs these from the header verbatim, so
   the correspondence proof (`ProcedureHasTypeAGen.lean`) only loses a `rfl`-level
   `typeArgs = []` obligation and otherwise stands. The disjointness conjunct is over
   keys, which `subst` does not change, so it transfers to the instantiated blocks for
   free (`(subst [σ] ·)` preserves `.keys`).

5. **`genCallStmt_mutableVars` (`ProcedureHasTypeAGen/MutableVars.lean:325`).**
   ModRights reasons about *names* (which vars the call writes: `Mσ.keys ++ T.keys`).
   Since `subst [σ]` preserves keys (`(s.M.map (subst[σ]·)).keys = s.M.keys`), the
   modified/defined-var sets are literally unchanged. Expect only a `.keys`-of-`map`
   rewrite (`ListMap.keys_eq_map_fst` + `List.map_map`) at the point where the
   instantiated block replaces the declared one; the structural proof is otherwise
   intact.

6. **Completeness (`StmtHasTypeAGenComplete.lean` + `genCallStmt_mem_complete`,
   `StmtHasTypeAGen.lean:467`).** `ProcSigComplete` drops `typeArgs = []` and gains
   "for the chosen `σ`" — i.e. a well-typed call is reachable at the instantiation the
   generator can sample. `CallOk`/`admissible` shape predicates
   (`StmtHasTypeAGenComplete.lean:176,263`) must accept the instantiated arg types.
   `genCallStmt_mem_complete` runs the `do`-block forward with the extra `sampledTys`
   membership step (mirror `genIndirPoly_complete`'s `sampledTys_mem_support`). This
   is the largest single piece; if #32's completeness note is a guide, the
   *spec-shaped* direction (every well-typed poly call reachable) may warrant its own
   follow-up, while the *generator-shaped* direction (every emitted poly call is in
   support) is mechanical.

### Harness / external callers

- `TestScaffold.lean:620` `genProcsWith`: feed **all** siblings (drop the
  `typeArgs.isEmpty` filter); `headerProcSig` now carries `typeArgs`.
- `TycheViz.lean`, `CmdHasTypeAGen/TestSupport.lean`, any `procs := []` call sites:
  no change (empty context is still valid; `[]` trivially satisfies the relaxed
  `ProcSigCorresponds`).

## Risk / effort notes

- **Effort:** the σ-generalization is mechanical but touches ~5 proof files, two of
  which (`GenCallStmtSound`, `StmtHasTypeAGen`) carry the delicate index/append
  arithmetic already noted in the procedure-gen memory. Budget for heartbeat bumps.
- **Capture:** the freshening of `s.typeArgs` vs. the enclosing rigid `tvars` is the
  one genuinely new correctness concern (the monomorphic path never had type vars to
  capture). Model it on `freshenBoundVars` and test empirically (à la #32's
  `#eval findPolymorphicOps` check) against a callee whose type-arg name collides with
  an enclosing one before trusting the proof.
- **Verify against the real checker:** as the procedure-gen work did, run generated
  polymorphic calls through `Statement.typeCheck` with a real `Program` holding the
  polymorphic callee, counting accepted/rejected, before declaring done.
- **Axiom hygiene:** target the same `[propext, Classical.choice, Quot.sound]` set;
  the σ-generalization introduces no new axiom surface (it only stops *using* the
  `subst_emptyS` simplification).
