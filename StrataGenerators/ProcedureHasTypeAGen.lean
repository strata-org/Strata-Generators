import StrataGenerators.ProcedureHasTypeAGen.Core
import StrataGenerators.ProcedureHasTypeAGen.Support
import StrataGenerators.ProcedureHasTypeAGen.MutableVars
import StrataGenerators.CmdHasTypeAGenSound
import Strata.Languages.Core.ProcedureTypeSpec

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen
open StrataGenerators.Stmt StrataGenerators.Function

/-!
# Soundness and completeness of `genProcedure`

`genProcedure` (in `ProcedureHasTypeAGen/Core.lean`) generates well-typed Strata
Core procedures. This file proves it **sound** and **complete** with respect to
the `ProcHasTypeA` typing relation of `Strata.Languages.Core.ProcedureTypeSpec`.

The proof is *compositional*: it reuses `genInputs_support`/`genInputs_complete`
(for the output signature, exactly as the function generator uses them for
inputs), `genStmtChain_sound` and the body's `genStmtChain` support membership
(for the body — completeness takes that membership as a hypothesis, dischargeable
via `spec_complete`), and `genStmtChain_mutableVars` (for the modification-rights
obligation).

## The context-alignment lemma

The one genuinely procedure-specific fact is `procBodyContext_default`: with
empty inputs, empty type-arguments, and no in-out parameters, the declarative
body context `procBodyContext Γ proc` (a single new scope binding inputs ++
outputs ++ old-bindings) collapses to `procToTCtx proc.header.outputs` — the very
context `genStmtChain_sound` produces when seeded with the output parameters. This is
what lets the generated body's `StatementsHasTypeA` line up *definitionally* with the
`ProcBodyHasType'.structured` obligation.
-/

namespace StrataGenerators.Procedure

/-- `Map.keys` and `ListMap.keys` are word-for-word identical definitions on the
    same underlying `List (α × β)`, but they are *distinct constants*, so a bridge
    is needed to move between the statement generator (which threads `Map.keys`)
    and the procedure typing spec (which uses `proc.header.outputs.keys`, i.e.
    `ListMap.keys`). -/
theorem Map_keys_eq_ListMap_keys {α β} (m : List (α × β)) :
    Map.keys m = ListMap.keys m := by
  induction m with
  | nil => rfl
  | cons p m ih => obtain ⟨a, b⟩ := p; simp only [Map.keys, ListMap.keys, ih]

/-- `ListMap.keys` distributes over the `ListMap` append (which is `List.append`).
    The `ListMap` `++` is not *syntactically* `List.append`, so `List.map_append`
    won't fire directly; we route through the `Map.keys` bridge. -/
theorem ListMap_keys_append (a b : ListMap (Identifier Unit) LMonoTy) :
    ListMap.keys (a ++ b) = ListMap.keys a ++ ListMap.keys b := by
  rw [← Map_keys_eq_ListMap_keys, ← Map_keys_eq_ListMap_keys, ← Map_keys_eq_ListMap_keys]
  exact Map.keys_append a b

/-- `Map.values` and `ListMap.values` are the same traversal of the same list. -/
theorem Map_values_eq_ListMap_values {α β} (m : List (α × β)) :
    Map.values m = ListMap.values m := by
  induction m with
  | nil => rfl
  | cons p m ih => obtain ⟨a, b⟩ := p; simp only [Map.values, ListMap.values, ih]

/-- `ListMap.values` distributes over the `ListMap` append. -/
theorem ListMap_values_append (a b : ListMap (Identifier Unit) LMonoTy) :
    (a ++ b).values = a.values ++ b.values := by
  show ListMap.values (List.append a b) = _
  rw [ListMap.values_eq_map_snd, ListMap.values_eq_map_snd, ListMap.values_eq_map_snd]
  simp [List.map_append]

/-- **In-out parameters.** For the three-block layout `inputs = M ++ I`,
    `outputs = M ++ O` (the shared block `M` leading both) with the three blocks
    mutually disjoint, the in-out parameters (`getInoutParams`, i.e. the inputs
    whose key is also an output key) are exactly the shared block `M`: every
    `M`-entry's key is an output key (`hM`), every `I`-entry's is not (`hI`). -/
theorem getInoutParams_inout (name : String) (tyArgs : List TyIdentifier)
    (M I O : List ((Identifier Unit) × LMonoTy))
    (hI : ∀ p ∈ I, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = false)
    (hM : ∀ p ∈ M, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = true) :
    ({ name := ⟨name, ()⟩, typeArgs := tyArgs, inputs := M ++ I, outputs := M ++ O,
       noFilter := false } : Procedure.Header).getInoutParams = M := by
  simp only [Procedure.Header.getInoutParams]
  show List.filter _ (M ++ I) = M
  rw [List.filter_append, List.filter_eq_self.mpr hM,
      List.filter_eq_nil_iff.mpr (by intro p hp; rw [hI p hp]; simp)]
  simp

/-- Rotating a three-way append is a permutation. (Lean core has `perm_append_comm` for
    two; this is the three-block instance the body-scope alignment needs.) -/
theorem perm_append_rotate {α} (a b c : List α) : (a ++ b ++ c).Perm (c ++ b ++ a) := by
  have h1 : (a ++ b ++ c).Perm (c ++ (a ++ b)) := List.perm_append_comm
  have h2 : (c ++ (a ++ b)).Perm (c ++ (b ++ a)) := List.Perm.append_left _ List.perm_append_comm
  have h3 : c ++ (b ++ a) = c ++ b ++ a := by rw [List.append_assoc]
  exact h3 ▸ (h1.trans h2)

/-- Lookups in an `HMap.ofList` depend only on the *set* of bindings, provided the list is
    *functional* (any two bindings for a key agree). Both the declarative body scope
    (`old ++ outputs ++ inputs`) and the generator-side one
    (`(inputs ++ outputs ++ old).reverse`) are functional permutations of one another —
    they are the same bindings in a different order — so they look up identically, which is
    all `TContext.Equiv` asks for. Structural equality is unavailable: a scope is an opaque
    hash map, and hash maps built by different insertion orders are different values. -/
theorem find?_ofList_perm_of_functional {α β} [BEq α] [LawfulBEq α] [Hashable α]
    [LawfulHashable α] {L1 L2 : List (α × β)} (hperm : L1.Perm L2)
    (hfun : ∀ (k : α) (v1 v2 : β), (k, v1) ∈ L1 → (k, v2) ∈ L1 → v1 = v2) (k : α) :
    Strata.Util.HMap.find? (Strata.Util.HMap.ofList L1) k
      = Strata.Util.HMap.find? (Strata.Util.HMap.ofList L2) k := by
  -- `find?` on `ofList` is `lookup` on the reversed list.
  have hrev : ∀ (L : List (α × β)),
      Strata.Util.HMap.find? (Strata.Util.HMap.ofList L) k = L.reverse.lookup k := by
    intro L
    have h := Freshening.find?_ofList_reverse L.reverse k
    rwa [List.reverse_reverse] at h
  -- A key that occurs at all has *some* binding.
  have hsome : ∀ (l : List (α × β)) (v : β), (k, v) ∈ l → ∃ w, l.lookup k = some w := by
    intro l v hv
    induction l with
    | nil => cases hv
    | cons p rest ih =>
      obtain ⟨a, b⟩ := p
      by_cases hk : k = a
      · exact ⟨b, by simp [hk]⟩
      · rcases List.mem_cons.mp hv with heq | hv'
        · exact absurd (congrArg Prod.fst heq) hk
        · obtain ⟨w, hw⟩ := ih hv'
          exact ⟨w, by
            simp only [List.lookup_cons, show (k == a) = false from by simp [hk], hw]⟩
  have hmem1 : ∀ v, (k, v) ∈ L2 → (k, v) ∈ L1 := fun v hv => hperm.mem_iff.mpr hv
  have hmem2 : ∀ v, (k, v) ∈ L1 → (k, v) ∈ L2 := fun v hv => hperm.mem_iff.mp hv
  rw [hrev L1, hrev L2]
  rcases h1 : L1.reverse.lookup k with _ | v1
  · rcases h2 : L2.reverse.lookup k with _ | v2
    · rfl
    · exfalso
      have hv2 : (k, v2) ∈ L1 :=
        hmem1 v2 (List.mem_reverse.mp (Freshening.lookup_mem _ _ _ h2))
      obtain ⟨w, hw⟩ := hsome L1.reverse v2 (List.mem_reverse.mpr hv2)
      rw [h1] at hw; exact absurd hw (by simp)
  · have hv1 : (k, v1) ∈ L1 := List.mem_reverse.mp (Freshening.lookup_mem _ _ _ h1)
    obtain ⟨w, hw⟩ := hsome L2.reverse v1 (List.mem_reverse.mpr (hmem2 v1 hv1))
    rw [hw]
    have hvw : (k, w) ∈ L1 :=
      hmem1 w (List.mem_reverse.mp (Freshening.lookup_mem _ _ _ hw))
    exact congrArg some (hfun k v1 w hv1 hvw)

/-- **Context alignment (in-out), Γ-parameterized.** For the three-block layout (shared
    block `M` leading both signatures) over an ambient type-scope `Γ` with `Γ.types = []`,
    the declarative body context `procBodyContext Γ proc` agrees with the single-scope
    `procToTCtxΓ Γ (inputs ++ outputs ++ oldVars M)`.

    Agreement is `TContext.Equiv`, not equality: `procBodyContext` builds its scope as
    `HMap.ofList (old ++ outputs ++ inputs)` while `procToTCtxΓ` builds
    `HMap.ofList ((inputs ++ outputs ++ old).reverse)`. Those are the same bindings in a
    different order — hence the same *lookups*, given that the seed is functional — but not
    the same hash-map value. `hfun` is the functionality of the seed, which
    `seed_functional` supplies at the call site. -/
theorem procBodyContext_inoutΓ (Γ : TContext Unit) (hΓtypes : Γ.types = [])
    (name : String) (tyArgs : List TyIdentifier)
    (M I O : List ((Identifier Unit) × LMonoTy))
    (hI : ∀ p ∈ I, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = false)
    (hM : ∀ p ∈ M, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = true)
    (hfun : Map.Functional
      (M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))))
    (pre post : ListMap CoreLabel Procedure.Check) (body : Procedure.Body) :
    TContext.Equiv (T := CoreLParams)
      (procBodyContext Γ
        { header := { name := ⟨name, ()⟩, typeArgs := tyArgs, inputs := M ++ I,
                      outputs := M ++ O, noFilter := false },
          spec := { preconditions := pre, postconditions := post },
          body := body })
      (procToTCtxΓ Γ (M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2)))) := by
  -- Spell the two scopes out: the spec builds `old ++ outputs ++ inputs`, we build the
  -- reverse of `inputs ++ outputs ++ old`. (`set` is unavailable — this file is
  -- Mathlib-free — so the blocks are written out.)
  have hperm :
      (((M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))).map
          (fun p => (p.1, LTy.forAll [] p.2))).reverse).Perm
      ((M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))).map
            (fun p => (p.1, LTy.forAll [] p.2))
        ++ (M ++ O).map (fun p => (p.1, LTy.forAll [] p.2))
        ++ (M ++ I).map (fun p => (p.1, LTy.forAll [] p.2))) := by
    refine (List.reverse_perm _).trans ?_
    simp only [List.map_append, List.map_map, Function.comp_def]
    exact perm_append_rotate _ _ _
  have hfun' : ∀ (k : Identifier Unit) (v1 v2 : LTy),
      (k, v1) ∈ (((M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))).map
          (fun p => (p.1, LTy.forAll [] p.2))).reverse) →
      (k, v2) ∈ (((M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))).map
          (fun p => (p.1, LTy.forAll [] p.2))).reverse) → v1 = v2 := by
    intro k v1 v2 h1 h2
    rw [List.mem_reverse] at h1 h2
    obtain ⟨p1, hp1, hpe1⟩ := List.mem_map.mp h1
    obtain ⟨p2, hp2, hpe2⟩ := List.mem_map.mp h2
    simp only [Prod.mk.injEq] at hpe1 hpe2
    obtain ⟨hk1, hv1⟩ := hpe1
    obtain ⟨hk2, hv2⟩ := hpe2
    rw [← hv1, ← hv2,
      hfun k p1.2 p2.2 (by rw [← hk1]; exact hp1) (by rw [← hk2]; exact hp2)]
  refine ⟨?_, rfl⟩
  rw [show (procBodyContext Γ
        { header := { name := ⟨name, ()⟩, typeArgs := tyArgs, inputs := M ++ I,
                      outputs := M ++ O, noFilter := false },
          spec := { preconditions := pre, postconditions := post },
          body := body }).types
      = [Strata.Util.HMap.ofList
          ((M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))).map
                (fun p => (p.1, LTy.forAll [] p.2))
            ++ (M ++ O).map (fun p => (p.1, LTy.forAll [] p.2))
            ++ (M ++ I).map (fun p => (p.1, LTy.forAll [] p.2)))] from by
    simp only [procBodyContext, hΓtypes, Strata.Util.HMaps.push,
      getInoutParams_inout name tyArgs M I O hI hM, List.map_map, Function.comp_def]]
  rw [show (procToTCtxΓ Γ
        (M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2)))).types
      = [Strata.Util.HMap.ofList
          (((M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))).map
            (fun p => (p.1, LTy.forAll [] p.2))).reverse)] from rfl]
  exact ⟨fun k => (find?_ofList_perm_of_functional hperm hfun' k).symm, True.intro⟩

/-- **Context alignment (in-out).** The `default`-ambient special case of
    `procBodyContext_inoutΓ` (`default.types = []`). -/
theorem procBodyContext_inout (name : String) (tyArgs : List TyIdentifier)
    (M I O : List ((Identifier Unit) × LMonoTy))
    (hI : ∀ p ∈ I, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = false)
    (hM : ∀ p ∈ M, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = true)
    (hfun : Map.Functional
      (M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))))
    (pre post : ListMap CoreLabel Procedure.Check) (body : Procedure.Body) :
    TContext.Equiv (T := CoreLParams)
      (procBodyContext (default)
        { header := { name := ⟨name, ()⟩, typeArgs := tyArgs, inputs := M ++ I,
                      outputs := M ++ O, noFilter := false },
          spec := { preconditions := pre, postconditions := post },
          body := body })
      (procToTCtx (M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2)))) :=
  procBodyContext_inoutΓ default rfl name tyArgs M I O hI hM hfun pre post body

-- ── Facts about `disjointInputs` ──────────────────────────────────────────

/-- After removing every input whose key collides with an output, no surviving
    input has an output key: filtering `disjointInputs ins outs` by output-key
    membership yields the empty list. This is the disjointness the body-context
    alignment needs (`getInoutParams = []`). -/
theorem disjointInputs_disjoint (ins outs : ListMap (Identifier Unit) LMonoTy) :
    ((disjointInputs ins outs).filter fun p => (ListMap.keys outs).contains p.1) = [] := by
  rw [List.filter_eq_nil_iff]
  intro p hp
  simp only [disjointInputs, List.mem_filter] at hp
  simpa only [Bool.not_eq_true', Bool.not_eq_false, Bool.not_eq_true] using hp.2

/-- A surviving key of `disjointInputs ins outs` is never an output key. -/
theorem disjointInputs_key_not_output (ins outs : ListMap (Identifier Unit) LMonoTy)
    (k : Identifier Unit) (hk : k ∈ ListMap.keys (disjointInputs ins outs)) :
    k ∉ ListMap.keys outs := by
  rw [ListMap.keys_eq_map_fst, List.mem_map] at hk
  obtain ⟨p, hp_mem, rfl⟩ := hk
  simp only [disjointInputs, List.mem_filter] at hp_mem
  have := hp_mem.2
  rw [Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem] at this
  exact this

/-- **Idempotence of `disjointInputs`.** When `X`'s keys are already disjoint from
    `Y`'s, filtering `X` by `Y`-key membership removes nothing: `disjointInputs X Y
    = X`. This is the completeness-side witness that a decomposed procedure's
    input-only / output-only blocks survive the generator's disjointness filters
    unchanged. -/
theorem disjointInputs_eq_self (X Y : ListMap (Identifier Unit) LMonoTy)
    (h : ∀ k ∈ ListMap.keys X, k ∉ ListMap.keys Y) : disjointInputs X Y = X := by
  simp only [disjointInputs]
  apply List.filter_eq_self.mpr
  intro p hp
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
  rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
  intro hmem
  exact h p.1 (by rw [ListMap.keys_eq_map_fst]; exact List.mem_map.mpr ⟨p, hp, rfl⟩) hmem

/-- `disjointInputs ins outs` is a *sublist* of `ins` (it only removes entries),
    so any property closed under sublists — e.g. `Nodup` of the keys or
    reachability of the values — transfers from `ins`. -/
theorem disjointInputs_sublist (ins outs : ListMap (Identifier Unit) LMonoTy) :
    List.Sublist (disjointInputs ins outs) ins :=
  List.filter_sublist

/-- The keys of `disjointInputs ins outs` are a sublist of `ins`'s keys. -/
theorem disjointInputs_keys_sublist (ins outs : ListMap (Identifier Unit) LMonoTy) :
    List.Sublist (ListMap.keys (disjointInputs ins outs)) (ListMap.keys ins) := by
  rw [ListMap.keys_eq_map_fst, ListMap.keys_eq_map_fst]
  exact (disjointInputs_sublist ins outs).map _

/-- `disjointInputs ins outs`'s keys are `Nodup` whenever `ins`'s keys are. -/
theorem disjointInputs_keys_nodup (ins outs : ListMap (Identifier Unit) LMonoTy)
    (h : (ListMap.keys ins).Nodup) : (ListMap.keys (disjointInputs ins outs)).Nodup :=
  (disjointInputs_keys_sublist ins outs).nodup h

/-- Every value of `disjointInputs ins outs` is a value of `ins`. -/
theorem disjointInputs_values_mem (ins outs : ListMap (Identifier Unit) LMonoTy)
    (ty : LMonoTy) (h : ty ∈ (disjointInputs ins outs).values) : ty ∈ ins.values := by
  rw [ListMap.values_eq_map_snd] at h ⊢
  exact (disjointInputs_sublist ins outs).map _ |>.subset h

/-- `Map.keys` distributes over append. -/
theorem Map_keys_append (m₁ m₂ : Map (Identifier Unit) LMonoTy) :
    Map.keys (m₁ ++ m₂) = Map.keys m₁ ++ Map.keys m₂ :=
  Map.keys_append m₁ m₂

/-- **The write-target containment.** A mutable key of `inputs ++ outputs` under
    the immutable set `inputs.keys` is always an *output* key. (A mutable key is a
    key of `inputs ++ outputs` that is not among `inputs.keys`; since the keys of
    the append split as `inputs.keys ++ outputs.keys`, dropping the input keys
    leaves exactly the output keys.) This is what turns the `writable`-based
    `genStmtChain_mutableVars` invariant into the `ProcHasType'.modRights` obligation —
    with **no** disjointness hypothesis needed. -/
theorem mem_writable_append_keys (ins outs : Map (Identifier Unit) LMonoTy)
    (immutableVars : List (Identifier Unit)) (hro : immutableVars = Map.keys ins)
    (k : Identifier Unit)
    (hk : k ∈ Map.keys (VarCtx.writable immutableVars (ins ++ outs))) :
    k ∈ Map.keys outs := by
  subst hro
  rw [mem_writable_keys_iff, Map_keys_append] at hk
  obtain ⟨hk_app, hk_ro⟩ := hk
  rw [Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem] at hk_ro
  rcases List.mem_append.mp hk_app with h | h
  · exact absurd h hk_ro
  · exact h

/-- **The in-out write-target containment.** For the body seed
    `A ++ B ++ C` under the immutable set `A.keys ++ C.keys`, every mutable key is
    a key of the *middle* block `B`. (A mutable key is a key of `A ++ B ++ C` that
    is neither an `A`-key nor a `C`-key — both immutable — so it must live in `B`.)
    Instantiated at `A := inputs`, `B := outputs`, `C := oldVars M`, this says
    every body-modified variable is an *output* key, discharging `modRights`. No
    disjointness hypothesis is needed. -/
theorem mem_writable_seed_keys (A B C : Map (Identifier Unit) LMonoTy)
    (immutableVars : List (Identifier Unit))
    (hro : immutableVars = Map.keys A ++ Map.keys C)
    (k : Identifier Unit)
    (hk : k ∈ Map.keys (VarCtx.writable immutableVars (A ++ B ++ C))) :
    k ∈ Map.keys B := by
  subst hro
  rw [mem_writable_keys_iff, Map_keys_append, Map_keys_append] at hk
  obtain ⟨hk_app, hk_ro⟩ := hk
  rw [Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem, List.mem_append] at hk_ro
  have hkA : k ∉ Map.keys A := fun h => hk_ro (Or.inl h)
  have hkC : k ∉ Map.keys C := fun h => hk_ro (Or.inr h)
  rcases List.mem_append.mp hk_app with h | h
  · rcases List.mem_append.mp h with hA | hB
    · exact absurd hA hkA
    · exact hB
  · exact absurd h hkC

-- ── Functionality of the in-out body seed ─────────────────────────────────

/-- `oldVars` only renames keys, so it has exactly `M`'s types. -/
theorem oldVars_values (M : ListMap (Identifier Unit) LMonoTy) :
    (oldVars M).values = M.values := by
  induction M with
  | nil => rfl
  | cons p M ih =>
    obtain ⟨a, b⟩ := p
    simp only [oldVars, List.map_cons, ListMap.values]
    rw [show ListMap.values (List.map (fun x => (CoreIdent.mkOld x.fst.name, x.snd)) M)
          = ListMap.values M from ih]

/-- Every key of `oldVars M` contains a space (`CoreIdent.mkOld` prefixes
    `"old "`). This is the fact that keeps `oldVars M` key-disjoint from the
    space-free generated parameter names of `M`/`I`/`O`. -/
theorem oldVars_key_space (M : ListMap (Identifier Unit) LMonoTy)
    (k : Identifier Unit) (hk : k ∈ Map.keys (oldVars M)) : ' ' ∈ k.name.toList := by
  simp only [oldVars, Map.keys_eq_map_fst, List.map_map, List.mem_map, Function.comp] at hk
  obtain ⟨p, _, rfl⟩ := hk
  -- `p.fst = (fun (id, ty) => (mkOld id.name, ty)) q).fst = mkOld q.1.name`
  simp only [CoreIdent.mkOld, CoreIdent.oldStr, String.toList_append]
  exact List.mem_append_left _ (by decide)

/-- The keys of `oldVars M` are `Nodup` whenever `M`'s keys are: `CoreIdent.mkOld`
    composed with `.name` is injective (a `Unit`-tagged identifier is determined by
    its name, and `mkOld` is injective on strings), so mapping over the `Nodup`
    key list preserves `Nodup`. -/
theorem oldVars_keys_nodup (M : ListMap (Identifier Unit) LMonoTy)
    (hM : (Map.keys M).Nodup) : (Map.keys (oldVars M)).Nodup := by
  rw [oldVars, Map.keys_eq_map_fst, List.map_map]
  rw [Map.keys_eq_map_fst] at hM
  -- `(oldVars M).keys = M.map (fun p => mkOld p.1.name)`, which factors through
  -- `M.keys = M.map Prod.fst` by an injective post-map.
  have hcomp : (Prod.fst ∘ fun (p : (Identifier Unit) × LMonoTy) => (CoreIdent.mkOld p.1.name, p.2))
      = (fun id : Identifier Unit => CoreIdent.mkOld id.name) ∘ Prod.fst := by
    funext p; rfl
  rw [hcomp, ← List.map_map]
  apply hM.map
  intro a b hab
  apply mt _ hab
  intro heq
  simp only [CoreIdent.mkOld, CoreIdent.oldStr, Identifier.mk.injEq, String.append_right_inj] at heq
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  cases a2; cases b2
  simp only at heq
  simp [heq]

/-- Two maps whose *keys* are drawn from disjoint character classes — one all
    space-free, the other all space-containing — share no key, so their append is
    functional whenever each half is. This is how `oldVars M` (space-containing
    keys) composes with the space-free generated signature. -/
theorem functional_append_of_space_disjoint
    (m₁ m₂ : Map (Identifier Unit) LMonoTy)
    (h₁ : Map.Functional m₁) (h₂ : Map.Functional m₂)
    (hs₁ : ∀ k ∈ Map.keys m₁, ' ' ∉ k.name.toList)
    (hs₂ : ∀ k ∈ Map.keys m₂, ' ' ∈ k.name.toList) :
    Map.Functional (m₁ ++ m₂) :=
  Map.functional_append m₁ m₂ h₁ h₂ (by
    intro x v₁ v₂ hx₁ hx₂
    exact absurd (hs₂ x (Map.mem_keys_of_mem m₂ x v₂ hx₂))
      (hs₁ x (Map.mem_keys_of_mem m₁ x v₁ hx₁)))

/-- **Functionality of the in-out body seed.** The seed `(M ++ I) ++ (M ++ O) ++
    oldVars M` is functional: the two signature halves `M ++ I` and `M ++ O` each
    have `Nodup` keys (hence are functional), and they agree on shared keys — a
    key common to both is neither an `I`-key (disjoint from `M ++ O`) nor an
    `O`-key (disjoint from `M ++ I`), so both entries come from the shared block
    `M`, where `Nodup` forces equality; and `oldVars M`'s space-containing keys
    are disjoint from the space-free generated names of `M`/`I`/`O`. -/
theorem seed_functional
    (M I O : ListMap (Identifier Unit) LMonoTy)
    (hMnodup : (Map.keys M).Nodup)
    (hInNodup : (Map.keys (M ++ I)).Nodup)
    (hOutNodup : (Map.keys (M ++ O)).Nodup)
    -- `I` shares no key with `M ++ O`, `O` shares no key with `M ++ I`:
    (hI_notMO : ∀ k ∈ Map.keys I, k ∉ Map.keys (M ++ O))
    (hO_notMI : ∀ k ∈ Map.keys O, k ∉ Map.keys (M ++ I))
    -- keys of M, I, O are space-free; keys of oldVars M contain a space:
    (hMs : ∀ k ∈ Map.keys M, ' ' ∉ k.name.toList)
    (hIs : ∀ k ∈ Map.keys I, ' ' ∉ k.name.toList)
    (hOs : ∀ k ∈ Map.keys O, ' ' ∉ k.name.toList) :
    Map.Functional (M ++ I ++ (M ++ O) ++ oldVars M) := by
  have hInFun : Map.Functional (M ++ I) := Map.functional_of_nodup _ hInNodup
  have hOutFun : Map.Functional (M ++ O) := Map.functional_of_nodup _ hOutNodup
  have hMFun : Map.Functional M := Map.functional_of_nodup _ hMnodup
  -- The two signature halves agree on shared keys.
  have hagree : ∀ (x : Identifier Unit) (v₁ v₂ : LMonoTy),
      List.Mem (x, v₁) (M ++ I) → List.Mem (x, v₂) (M ++ O) → v₁ = v₂ := by
    intro x v₁ v₂ hx₁ hx₂
    -- `x` is a key of `M ++ O`, so it is not an `I`-key ⇒ `(x,v₁) ∈ M`.
    have hxMO : x ∈ Map.keys (M ++ O) := Map.mem_keys_of_mem _ x v₂ hx₂
    have hxnI : x ∉ Map.keys I := fun hI => hI_notMO x hI hxMO
    have hm₁ : List.Mem (x, v₁) M := Map.mem_left_of_append_not_mem_keys M I x v₁ hx₁ hxnI
    -- `x` is a key of `M ++ I`, so it is not an `O`-key ⇒ `(x,v₂) ∈ M`.
    have hxMI : x ∈ Map.keys (M ++ I) := Map.mem_keys_of_mem _ x v₁ hx₁
    have hxnO : x ∉ Map.keys O := fun hO => hO_notMI x hO hxMI
    have hm₂ : List.Mem (x, v₂) M := Map.mem_left_of_append_not_mem_keys M O x v₂ hx₂ hxnO
    exact hMFun x v₁ v₂ hm₁ hm₂
  have hSigFun : Map.Functional (M ++ I ++ (M ++ O)) :=
    Map.functional_append (M ++ I) (M ++ O) hInFun hOutFun hagree
  -- The signature keys are all space-free.
  have hSigSpace : ∀ k ∈ Map.keys (M ++ I ++ (M ++ O)), ' ' ∉ k.name.toList := by
    intro k hk
    rw [show Map.keys (M ++ I ++ (M ++ O)) = Map.keys (M ++ I) ++ Map.keys (M ++ O)
          from Map.keys_append _ _, List.mem_append] at hk
    rcases hk with h | h
    · rw [show Map.keys (M ++ I) = Map.keys M ++ Map.keys I from Map.keys_append _ _,
          List.mem_append] at h
      rcases h with h | h
      · exact hMs k h
      · exact hIs k h
    · rw [show Map.keys (M ++ O) = Map.keys M ++ Map.keys O from Map.keys_append _ _,
          List.mem_append] at h
      rcases h with h | h
      · exact hMs k h
      · exact hOs k h
  exact functional_append_of_space_disjoint (M ++ I ++ (M ++ O)) (oldVars M)
    hSigFun (Map.functional_of_nodup _ (oldVars_keys_nodup M hMnodup)) hSigSpace
    (oldVars_key_space M)

-- ── Support / completeness of `genChecks` ─────────────────────────────────

/-- The `mapM` inside `genChecks` produces a `ListMap` whose every value's `expr`
    is a `bool` expression in the support of `genLExpr … .bool`. -/
theorem mapM_genChecks_values (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) (depth : Nat)
    (labels : List CoreLabel) (m : ListMap CoreLabel Procedure.Check) (pctx : PolyOpCtx := [])
    (hm : m ∈ SetGen.support
      (labels.mapM (m := SetGen.Set) (fun l => do
        let e ← genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth .bool
        pure (l, ({ expr := e } : Procedure.Check))))) :
    ∀ c ∈ m.values, c.expr ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth .bool) := by
  induction labels generalizing m with
  | nil =>
    simp only [List.mapM_nil] at hm
    subst hm
    intro c hc; simp only [ListMap.values, List.not_mem_nil] at hc
  | cons l ls ih =>
    simp only [List.mapM_cons] at hm
    obtain ⟨pair, hpair, rest, hrest, rfl⟩ := hm
    obtain ⟨e, he, rfl⟩ := hpair
    intro c hc
    simp only [ListMap.values, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact he
    · exact ih rest hrest c (by simpa only [ListMap.values] using hc)

/-- Membership in `genChecks octx tvars depth`: every clause's `expr` is a `bool`
    expression reachable by `genLExpr`. -/
theorem genChecks_support (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap CoreLabel Procedure.Check) (pctx : PolyOpCtx := [])
    (hm : m ∈ SetGen.support (genChecks (G := SetGen.Set) fctx octx tvars depth pctx)) :
    ∀ c ∈ m.values, c.expr ∈ SetGen.support
      (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth .bool) := by
  simp only [genChecks, mem_support_bind_iff] at hm
  obtain ⟨labels, _, hm⟩ := hm
  exact mapM_genChecks_values fctx octx tvars depth labels m pctx hm

/-- Reverse of `mapM_genChecks_values`: a `ListMap` of checks whose every `expr`
    is reachable by `genLExpr … .bool` is in the support of the `mapM` inside
    `genChecks`, run over its own keys. -/
theorem mapM_genChecks_complete (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap CoreLabel Procedure.Check)
    (hattr : ∀ c ∈ m.values, c.attr = .Default)
    (hmd : ∀ c ∈ m.values, c.md = #[])
    (hvals : ∀ c ∈ m.values, c.expr ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool)) :
    m ∈ SetGen.support
      (m.keys.mapM (m := SetGen.Set) (fun l => do
        let e ← genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool
        pure (l, ({ expr := e } : Procedure.Check)))) := by
  induction m with
  | nil =>
    show [] ∈ SetGen.support (pure [] : SetGen.Set _)
    rw [mem_support_pure_iff]
  | cons p rest ih =>
    obtain ⟨l, c⟩ := p
    simp only [ListMap.keys, List.mapM_cons]
    have hc_mem : c ∈ ListMap.values ((l, c) :: rest) := by simp [ListMap.values]
    have hce := hvals c hc_mem
    have hrest : ∀ c' ∈ ListMap.values rest,
        c'.expr ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool) := by
      intro c' hc'; exact hvals c' (by simp only [ListMap.values, List.mem_cons]; exact Or.inr hc')
    have hrest_attr : ∀ c' ∈ ListMap.values rest, c'.attr = .Default := by
      intro c' hc'; exact hattr c' (by simp only [ListMap.values, List.mem_cons]; exact Or.inr hc')
    have hrest_md : ∀ c' ∈ ListMap.values rest, c'.md = #[] := by
      intro c' hc'; exact hmd c' (by simp only [ListMap.values, List.mem_cons]; exact Or.inr hc')
    -- The head check `{ expr := c.expr }` (which `pure` produces) equals `c`, since
    -- `c`'s `attr`/`md` are at defaults.
    have hc_eq : ({ expr := c.expr } : Procedure.Check) = c := by
      have ha := hattr _ hc_mem
      have hmm := hmd _ hc_mem
      cases c with
      | mk e a md => subst ha; subst hmm; rfl
    -- Witness the actual head pair `(l, c)`; its membership in the generator's
    -- head step holds because `pure` produces `(l, { expr := c.expr }) = (l, c)`.
    refine ⟨(l, c), ⟨c.expr, hce, ?_⟩, rest, ih hrest_attr hrest_md hrest, rfl⟩
    show (l, c) ∈ SetGen.support (pure (l, ({ expr := c.expr } : Procedure.Check)) : SetGen.Set _)
    rw [mem_support_pure_iff, hc_eq]

/-- Completeness of `genChecks`: a check `ListMap` whose labels' names are
    reachable by `genNameList`, whose clauses are all default-`attr`/empty-`md`,
    and whose every `expr` is reachable by `genLExpr … .bool`, is in the support
    of `genChecks`. -/
theorem genChecks_complete (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap CoreLabel Procedure.Check)
    (hlabels : m.keys ∈ SetGen.support (genNameList (G := SetGen.Set) depth))
    (hattr : ∀ c ∈ m.values, c.attr = .Default)
    (hmd : ∀ c ∈ m.values, c.md = #[])
    (hvals : ∀ c ∈ m.values, c.expr ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool)) :
    m ∈ SetGen.support (genChecks (G := SetGen.Set) fctx octx tvars depth) := by
  simp only [genChecks, mem_support_bind_iff]
  exact ⟨m.keys, hlabels, mapM_genChecks_complete fctx octx tvars depth m hattr hmd hvals⟩

-- ── rigidTypeVars weakening ───────────────────────────────────────────────

/-- **`RigidAnnotCompat` is antitone in `rigidVars`.** Shrinking the rigid-variable
    set only *weakens* the "σ is identity on rigid vars" constraint on the
    witnessing substitution, so the same σ still works. No reflexivity or
    generator-specific fact is needed. -/
theorem RigidAnnotCompat.weaken {aliases : List TypeAlias} {rv1 rv2 : List TyIdentifier}
    {ann mty : LMonoTy} (h : RigidAnnotCompat aliases rv1 ann mty) (hsub : rv2 ⊆ rv1) :
    RigidAnnotCompat aliases rv2 ann mty := by
  obtain ⟨σ, hfix, haeq⟩ := h
  exact ⟨σ, fun v hv => hfix v (hsub hv), haeq⟩

/-- **`CmdHasType'` rigidTypeVars weakening.** The ambient `C` is consumed by
    `CmdHasType'` (under `instHasTypeA`) only via `C.rigidTypeVars` in the
    `RigidAnnotCompat` premise of the `init` cases (`exprTyped` ignores `C`), so
    replacing `C.rigidTypeVars` by any subset `rv` preserves typing. `CmdHasType'`
    leaves `C` untouched in its output, so only `Γ` threads through. -/
theorem CmdHasTypeA_weaken_rigid {C : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {c : Cmd Expression} {rv : List TyIdentifier}
    (h : CmdHasTypeA C Γ c Γ') (hsub : rv ⊆ C.rigidTypeVars) :
    CmdHasTypeA { C with rigidTypeVars := rv } Γ c Γ' := by
  cases h with
  | init_det x xty e mty tys md _Δ hfresh hnovar hlen hcompat hwk hexpr hequiv =>
    exact CmdHasType'.init_det _ x xty e mty tys md _ hfresh hnovar hlen
      (RigidAnnotCompat.weaken hcompat hsub) hwk hexpr hequiv
  | init_nondet x xty mty tys md _Δ hfresh hlen hcompat hwk hequiv =>
    exact CmdHasType'.init_nondet _ x xty mty tys md _ hfresh hlen
      (RigidAnnotCompat.weaken hcompat hsub) hwk hequiv
  | set_det x mty e md _Δ hfind hexpr hequiv =>
    exact CmdHasType'.set_det _ x mty e md _ hfind hexpr hequiv
  | set_nondet x mty md _Δ hfind hequiv => exact CmdHasType'.set_nondet _ x mty md _ hfind hequiv
  | assert l e md _Δ hexpr hequiv => exact CmdHasType'.assert _ l e md _ hexpr hequiv
  | assume l e md _Δ hexpr hequiv => exact CmdHasType'.assume _ l e md _ hexpr hequiv
  | cover l e md _Δ hexpr hequiv => exact CmdHasType'.cover _ l e md _ hexpr hequiv

/-- **`CmdExtHasType'` rigidTypeVars weakening.** The `cmd` case delegates to
    `CmdHasTypeA_weaken_rigid`; the `call` case's use of `C` is only through
    `S.exprTyped C …` (which, under `instHasTypeA`, ignores `C`) and is otherwise
    context-blind, so the very same witnesses transport. -/
theorem CmdExtHasTypeA_weaken_rigid {P : Program} {C : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {c : Command} {rv : List TyIdentifier}
    (h : CmdExtHasTypeA C P Γ c Γ') (hsub : rv ⊆ C.rigidTypeVars) :
    CmdExtHasTypeA { C with rigidTypeVars := rv } P Γ c Γ' := by
  cases h with
  | cmd _ c0 hcmd =>
    exact CmdExtHasType'.cmd _ _ c0 (CmdHasTypeA_weaken_rigid hcmd hsub)
  | call pname callArgs proc md σ _Δ hfind hInLen hOutLen hLhs hIn hOut hInout hequiv =>
    exact CmdExtHasType'.call _ pname callArgs proc md σ _ hfind hInLen hOutLen hLhs
      hIn hOut hInout hequiv

/-- **`FuncHasTypeA` is ambient-`C`-irrelevant.** Under `instHasTypeA`, every field
    of `FuncHasType'` either ignores `C` (nodup/undeclared-vars are syntactic) or
    uses it only through `S.exprTyped C … = HasTypeA [] …`, which drops `C`. So the
    predicate transports across any change of ambient context. -/
theorem FuncHasTypeA_C_irrel {C C' : LContext CoreLParams} {Γ : TContext Unit}
    {func : Function} (h : FuncHasTypeA C Γ func)
    -- `signatureWellKinded` reads the ambient context — but only its `knownTypes`, so any
    -- change that keeps those (e.g. swapping `rigidTypeVars`) carries it across.
    (hkt : C'.knownTypes = C.knownTypes) : FuncHasTypeA C' Γ func :=
  { inputsNodup := h.inputsNodup
    typeArgsNodup := h.typeArgsNodup
    noUndeclaredVars := h.noUndeclaredVars
    signatureWellKinded := by
      intro ty hty
      obtain ⟨ty', hcompat, hwk⟩ := h.signatureWellKinded ty hty
      refine ⟨ty', hcompat, ?_⟩
      unfold LContext.WellKindedTy at hwk ⊢
      rw [hkt]; exact hwk
    bodyTyped := h.bodyTyped
    measureTyped := h.measureTyped }

/-- **`StatementHasType'`/`StatementsHasType'` rigidTypeVars weakening** (annotated spec).
    The ambient `C.rigidTypeVars` flows *unchanged* through every statement
    constructor (`funcDecl` extends only `C.functions`, `typeDecl` only
    `C.knownTypes`; neither touches `rigidTypeVars`), and it is consumed only
    inside `cmd`'s `init` `RigidAnnotCompat`. So replacing `C.rigidTypeVars` by any
    subset `rv` — and, in the output context, the same `rv` — preserves typing.
    Proved by mutual induction on the derivation. -/
theorem StatementHasTypeA_rigid_eq {P : Program} {C C' : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {L : List String} {s : Statement}
    (h : StatementHasTypeA P C Γ L s C' Γ') : C'.rigidTypeVars = C.rigidTypeVars := by
  cases h with
  | cmd => rfl
  | block => rfl
  | ite_det => rfl
  | ite_nondet => rfl
  | loop => rfl
  | exit => rfl
  | funcDecl _ _ _ decl func md _ h_nrec h_func _ =>
    simp only [LContext.addFactoryFunction]; split <;> rfl
  | typeDecl _ C0' _ _ tc md _ h_add _ =>
    simp only [LContext.addKnownTypeWithError, Bind.bind, Except.bind] at h_add
    split at h_add
    · simp only [reduceCtorEq] at h_add
    · injection h_add with h_add_eq; rw [← h_add_eq]

theorem StatementHasTypeA_weaken_rigid {P : Program} {C C' : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {L : List String} {s : Statement} {rv : List TyIdentifier}
    (h : StatementHasTypeA P C Γ L s C' Γ') (hsub : rv ⊆ C.rigidTypeVars) :
    StatementHasTypeA P { C with rigidTypeVars := rv } Γ L s { C' with rigidTypeVars := rv } Γ' := by
  revert hsub
  induction h using StatementHasType'.rec
    (motive_2 := fun C Γ L ss C' Γ' (_ : StatementsHasTypeA P C Γ L ss C' Γ') =>
      rv ⊆ C.rigidTypeVars →
      StatementsHasTypeA P { C with rigidTypeVars := rv } Γ L ss { C' with rigidTypeVars := rv } Γ') with
  | cmd C Γ Γ2 L c Δ hc hequiv =>
    intro hsub
    exact StatementHasType'.cmd _ Γ Γ2 L c Δ (CmdExtHasTypeA_weaken_rigid hc hsub) hequiv
  | block C Γ C_body Γ_body L label body md Δ hlab hbody hequiv ih =>
    intro hsub
    exact StatementHasType'.block _ Γ { C_body with rigidTypeVars := rv } Γ_body L label body md
      Δ hlab (ih hsub) hequiv
  | ite_det C Γ C_t Γ_t C_e Γ_e L cond thenb elseb md Δ hcond hthen helse hequiv iht ihe =>
    intro hsub
    exact StatementHasType'.ite_det _ Γ { C_t with rigidTypeVars := rv } Γ_t
      { C_e with rigidTypeVars := rv } Γ_e L cond thenb elseb md Δ hcond (iht hsub) (ihe hsub)
      hequiv
  | ite_nondet C Γ C_t Γ_t C_e Γ_e L thenb elseb md Δ hthen helse hequiv iht ihe =>
    intro hsub
    exact StatementHasType'.ite_nondet _ Γ { C_t with rigidTypeVars := rv } Γ_t
      { C_e with rigidTypeVars := rv } Γ_e L thenb elseb md Δ (iht hsub) (ihe hsub) hequiv
  | loop C Γ C_body Γ_body L guard measure invariants body md Δ hg hm hi hbody hequiv ih =>
    intro hsub
    exact StatementHasType'.loop _ Γ { C_body with rigidTypeVars := rv } Γ_body L guard measure
      invariants body md Δ hg hm hi (ih hsub) hequiv
  | exit C Γ L label md Δ hmem hequiv =>
    intro _; exact StatementHasType'.exit _ Γ L label md Δ hmem hequiv
  | funcDecl C Γ L decl func md Δ hrec hfunc hequiv =>
    intro _
    -- `addFactoryFunction` leaves `rigidTypeVars` untouched, so the output context
    -- is `{ (C.addFactoryFunction …) with rigidTypeVars := rv }`.
    have hcong : ({ C with rigidTypeVars := rv } : LContext CoreLParams).addFactoryFunction func.toLFunc
        = { C.addFactoryFunction func.toLFunc with rigidTypeVars := rv } := by
      simp only [LContext.addFactoryFunction]; split <;> rfl
    rw [← hcong]
    exact StatementHasType'.funcDecl _ Γ L decl func md Δ hrec
      (FuncHasTypeA_C_irrel hfunc rfl) hequiv
  | typeDecl C C0' Γ L tc md Δ hadd hequiv =>
    intro _
    -- `addKnownTypeWithError` leaves `rigidTypeVars` untouched.
    have hcong : ({ C with rigidTypeVars := rv } : LContext CoreLParams).addKnownTypeWithError
        { name := tc.name, metadata := tc.numargs } default
        = .ok { C0' with rigidTypeVars := rv } := by
      simp only [LContext.addKnownTypeWithError, Bind.bind, Except.bind] at hadd ⊢
      split at hadd
      · simp only [reduceCtorEq] at hadd
      · injection hadd with hadd_eq; subst hadd_eq; rfl
    exact StatementHasType'.typeDecl _ { C0' with rigidTypeVars := rv } Γ L tc md Δ hcong hequiv
  | nil C Γ L Δ hequiv =>
    exact StatementsHasType'.nil (τ := LMonoTy) (P := P) _ Γ L Δ hequiv
  | cons C C' C'' Γ Γ' Γ'' L s ss hs hss ihs ihss =>
    rename_i hsub
    -- `hs`'s output `C'` has the same rigidTypeVars as `C` (statement typing
    -- preserves them), so the tail's subset hypothesis is discharged.
    have hrig : C'.rigidTypeVars = C.rigidTypeVars := StatementHasTypeA_rigid_eq hs
    exact StatementsHasType'.cons _ { C' with rigidTypeVars := rv } _ Γ Γ' Γ'' L s ss
      (ihs hsub) (ihss (hrig ▸ hsub))

/-- **`StatementsHasType'` rigidTypeVars weakening** (list form), specializing the
    mutual induction above. -/
theorem StatementsHasTypeA_weaken_rigid {P : Program} {C C' : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {L : List String} {ss : List Statement} {rv : List TyIdentifier}
    (h : StatementsHasTypeA P C Γ L ss C' Γ') (hsub : rv ⊆ C.rigidTypeVars) :
    StatementsHasTypeA P { C with rigidTypeVars := rv } Γ L ss { C' with rigidTypeVars := rv } Γ' := by
  revert hsub
  induction h using StatementsHasType'.rec
    (motive_1 := fun C Γ L s C' Γ' (_ : StatementHasTypeA P C Γ L s C' Γ') =>
      rv ⊆ C.rigidTypeVars →
      StatementHasTypeA P { C with rigidTypeVars := rv } Γ L s { C' with rigidTypeVars := rv } Γ') with
  | cmd C Γ Γ2 L c Δ hc hequiv =>
    rename_i hsub
    exact StatementHasType'.cmd _ Γ Γ2 L c Δ (CmdExtHasTypeA_weaken_rigid hc hsub) hequiv
  | block C Γ C_body Γ_body L label body md Δ hlab hbody hequiv ih =>
    rename_i hsub
    exact StatementHasType'.block _ Γ { C_body with rigidTypeVars := rv } Γ_body L label body md
      Δ hlab (ih hsub) hequiv
  | ite_det C Γ C_t Γ_t C_e Γ_e L cond thenb elseb md Δ hcond hthen helse hequiv iht ihe =>
    rename_i hsub
    exact StatementHasType'.ite_det _ Γ { C_t with rigidTypeVars := rv } Γ_t
      { C_e with rigidTypeVars := rv } Γ_e L cond thenb elseb md Δ hcond (iht hsub) (ihe hsub)
      hequiv
  | ite_nondet C Γ C_t Γ_t C_e Γ_e L thenb elseb md Δ hthen helse hequiv iht ihe =>
    rename_i hsub
    exact StatementHasType'.ite_nondet _ Γ { C_t with rigidTypeVars := rv } Γ_t
      { C_e with rigidTypeVars := rv } Γ_e L thenb elseb md Δ (iht hsub) (ihe hsub) hequiv
  | loop C Γ C_body Γ_body L guard measure invariants body md Δ hg hm hi hbody hequiv ih =>
    rename_i hsub
    exact StatementHasType'.loop _ Γ { C_body with rigidTypeVars := rv } Γ_body L guard measure
      invariants body md Δ hg hm hi (ih hsub) hequiv
  | exit C Γ L label md Δ hmem hequiv =>
    exact StatementHasType'.exit _ Γ L label md Δ hmem hequiv
  | funcDecl C Γ L decl func md Δ hrec hfunc hequiv =>
    have hcong : ({ C with rigidTypeVars := rv } : LContext CoreLParams).addFactoryFunction func.toLFunc
        = { C.addFactoryFunction func.toLFunc with rigidTypeVars := rv } := by
      simp only [LContext.addFactoryFunction]; split <;> rfl
    rw [← hcong]
    exact StatementHasType'.funcDecl _ Γ L decl func md Δ hrec
      (FuncHasTypeA_C_irrel hfunc rfl) hequiv
  | typeDecl C C0' Γ L tc md Δ hadd hequiv =>
    have hcong : ({ C with rigidTypeVars := rv } : LContext CoreLParams).addKnownTypeWithError
        { name := tc.name, metadata := tc.numargs } default
        = .ok { C0' with rigidTypeVars := rv } := by
      simp only [LContext.addKnownTypeWithError, Bind.bind, Except.bind] at hadd ⊢
      split at hadd
      · simp only [reduceCtorEq] at hadd
      · injection hadd with hadd_eq; subst hadd_eq; rfl
    exact StatementHasType'.typeDecl _ { C0' with rigidTypeVars := rv } Γ L tc md Δ hcong hequiv
  | nil C Γ L Δ hequiv =>
    intro _; exact StatementsHasType'.nil (τ := LMonoTy) (P := P) _ Γ L Δ hequiv
  | cons C C' C'' Γ Γ' Γ'' L s ss hs hss ihs ihss =>
    intro hsub
    have hrig : C'.rigidTypeVars = C.rigidTypeVars := StatementHasTypeA_rigid_eq hs
    exact StatementsHasType'.cons _ { C' with rigidTypeVars := rv } _ Γ Γ' Γ'' L s ss
      (ihs hsub) (ihss (hrig ▸ hsub))

-- ── Soundness ────────────────────────────────────────────────────────────

set_option maxHeartbeats 800000 in
/-- **Soundness of `genProcedure`.** Every procedure in the generator's support
    is well-typed w.r.t. `ProcHasTypeA` for any program `P` (and any ambient
    context `C`) whose callable procedures the threaded call-target context `procs`
    faithfully describes, i.e. `ProcSigCorresponds procs P`. That is the only
    side-condition (it is *vacuous* — `∀ s ∈ [], …` — when `procs = []`, recovering
    the old side-condition-free statement for a call-free body); it feeds straight
    into `genStmtChain_sound`, which the `.call` case of the body soundness needs to
    certify each emitted `call` against `P`.

    - `typeArgsNodup` — from `genTypeArgs_nodup`.
    - `inputsNodup` — from `genInputs_support` (input keys `Nodup`) carried across
      the `disjointInputs` filter (a sublist, so still `Nodup`).
    - `outputsNodup` — from `genInputs_support` (the output keys are `Nodup`).
    - `noUndeclaredVars` — every input/output type's ftvars lie in `typeArgs`
      (from `genLMonoTy typeArgs`); the filtered inputs' values are a subset of
      the raw inputs' values.
    - `preconditionsTyped` / `postconditionsTyped` — under `instHasTypeA` both
      reduce to `HasTypeA [] c.expr bool`, exactly what `genLExpr … .bool`
      produces.
    - `bodyTyped` — from `genStmtChain_sound`, using `procBodyContext_default` (valid
      because the filtered inputs are disjoint from the outputs) to identify the
      body context with `procToTCtx (inputs ++ outputs) = procStmtEnv.toTCtx
      (inputs ++ outputs)`.
    - `modRights` — from `genStmtChain_mutableVars`: every modified variable is a
      *mutable* key of `inputs ++ outputs` (hence an output key, via
      `mem_writable_append_keys`) or a body-defined variable. -/
theorem genProcedure_sound (P : Program) (octx : OpCtx) (procs : ProcSigCtx)
    (hProcs : ProcSigCorresponds procs P) (size len : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit) (hΓtypes : Γ.types = [])
    -- Upstream's `init` rules and `ProcHasType'.signatureWellKinded` need every stored /
    -- declared monotype to be well-kinded in the ambient context. `hC` covers the
    -- procedure's own signature (the generator makes all of the types); `hWK` is the
    -- statement-level premise — see the note on `StmtHasTypeAGen.WellKindedOk`. Only its
    -- *ambient* half is assumed: the scope-local half holds at the body seed because that
    -- scope holds nothing but generated signature types (`hseedWK` below), and it is
    -- carried along the body by `wellKindedOk_preserved`.
    (hC : SimpleTyArities C)
    (hWK : ∀ rv : List TyIdentifier,
      StrataGenerators.Stmt.WellKindedAmbient octx procs { C with rigidTypeVars := rv })
    (proc : Procedure) (pctx : PolyOpCtx := [])
    (hproc : proc ∈ SetGen.support
      (genProcedure (G := SetGen.Set) octx procs C Γ size len pctx)) :
    ProcHasTypeA P { C with rigidTypeVars := proc.header.typeArgs } Γ proc := by
  simp only [genProcedure, mem_support_bind_iff, mem_support_pure_iff] at hproc
  obtain ⟨name, _hname, typeArgs, htypeArgs, M, hM, rawInputOnly, hrawInputOnly,
          rawOutputOnly, hrawOutputOnly, pre, hpre, post, hpost,
          ⟨body, C', ctx'⟩, hbody, rfl⟩ := hproc
  -- The three signature blocks: `M` (in-out), `I := disjointInputs rawInputOnly M`
  -- (input-only), `O := disjointInputs rawOutputOnly (M ++ I)` (output-only). `set`
  -- is unavailable, so these derived terms appear in full below.
  -- Facts about `typeArgs` and the three generated blocks.
  have htyNodup : typeArgs.Nodup := genTypeArgs_nodup size typeArgs htypeArgs
  obtain ⟨hMKeysNodup, hMVals⟩ := genInputs_support typeArgs size M hM
  obtain ⟨hRawInKeysNodup, hRawInVals⟩ := genInputs_support typeArgs size rawInputOnly hrawInputOnly
  obtain ⟨hRawOutKeysNodup, hRawOutVals⟩ := genInputs_support typeArgs size rawOutputOnly hrawOutputOnly
  have hIKeysNodup : (ListMap.keys (disjointInputs rawInputOnly M)).Nodup :=
    disjointInputs_keys_nodup rawInputOnly M hRawInKeysNodup
  have hOKeysNodup :
      (ListMap.keys (disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M))).Nodup :=
    disjointInputs_keys_nodup rawOutputOnly (M ++ disjointInputs rawInputOnly M) hRawOutKeysNodup
  -- `inputsNodup` / `outputsNodup`: each is an append of two disjoint `Nodup` blocks.
  have hInputsNodup : (ListMap.keys (M ++ disjointInputs rawInputOnly M)).Nodup := by
    rw [ListMap_keys_append, List.nodup_append]
    refine ⟨hMKeysNodup, hIKeysNodup, ?_⟩
    intro a ha b hb hab
    exact disjointInputs_key_not_output rawInputOnly M b hb (hab ▸ ha)
  have hOutputsNodup :
      (ListMap.keys (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M))).Nodup := by
    rw [ListMap_keys_append, List.nodup_append]
    refine ⟨hMKeysNodup, hOKeysNodup, ?_⟩
    intro a ha b hb hab
    refine disjointInputs_key_not_output rawOutputOnly (M ++ disjointInputs rawInputOnly M) b hb ?_
    rw [ListMap_keys_append, List.mem_append]; exact Or.inl (hab ▸ ha)
  -- Space-freeness of the three blocks' keys (generated names have no space).
  have hMs : ∀ k ∈ Map.keys M, ' ' ∉ k.name.toList := by
    intro k hk; rw [Map_keys_eq_ListMap_keys] at hk
    exact genInputs_key_no_space typeArgs size M hM k hk
  have hIs : ∀ k ∈ Map.keys (disjointInputs rawInputOnly M), ' ' ∉ k.name.toList := by
    intro k hk; rw [Map_keys_eq_ListMap_keys] at hk
    exact genInputs_key_no_space typeArgs size rawInputOnly hrawInputOnly k
      ((disjointInputs_keys_sublist rawInputOnly M).subset hk)
  have hOs : ∀ k ∈ Map.keys (disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)),
      ' ' ∉ k.name.toList := by
    intro k hk; rw [Map_keys_eq_ListMap_keys] at hk
    exact genInputs_key_no_space typeArgs size rawOutputOnly hrawOutputOnly k
      ((disjointInputs_keys_sublist rawOutputOnly (M ++ disjointInputs rawInputOnly M)).subset hk)
  -- Cross-block disjointness (`Map.keys` form) for `seed_functional`.
  have hI_notMO : ∀ k ∈ Map.keys (disjointInputs rawInputOnly M),
      k ∉ Map.keys (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) := by
    intro k hk; rw [Map_keys_eq_ListMap_keys] at hk
    rw [Map_keys_eq_ListMap_keys, ListMap_keys_append, List.mem_append]
    rintro (hMk | hOk)
    · exact disjointInputs_key_not_output rawInputOnly M k hk hMk
    · refine disjointInputs_key_not_output rawOutputOnly (M ++ disjointInputs rawInputOnly M) k hOk ?_
      rw [ListMap_keys_append, List.mem_append]; exact Or.inr hk
  have hO_notMI : ∀ k ∈ Map.keys (disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)),
      k ∉ Map.keys (M ++ disjointInputs rawInputOnly M) := by
    intro k hk; rw [Map_keys_eq_ListMap_keys] at hk; rw [Map_keys_eq_ListMap_keys]
    exact disjointInputs_key_not_output rawOutputOnly (M ++ disjointInputs rawInputOnly M) k hk
  -- `Map.keys`-form `Nodup`s (bridge from the `ListMap.keys` forms above).
  have hMKeysNodup' : (Map.keys M).Nodup := by rw [Map_keys_eq_ListMap_keys]; exact hMKeysNodup
  have hInNodup' : (Map.keys (M ++ disjointInputs rawInputOnly M)).Nodup := by
    rw [Map_keys_eq_ListMap_keys]; exact hInputsNodup
  have hOutNodup' :
      (Map.keys (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M))).Nodup := by
    rw [Map_keys_eq_ListMap_keys]; exact hOutputsNodup
  -- The threaded soundness invariant: the in-out body seed is `Functional`.
  have hseedFun : Map.Functional
      (M ++ disjointInputs rawInputOnly M ++
        (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) ++ oldVars M) :=
    seed_functional M (disjointInputs rawInputOnly M)
      (disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M))
      hMKeysNodup' hInNodup' hOutNodup' hI_notMO hO_notMI hMs hIs hOs
  -- `contains`-forms of the block-membership facts (`getInoutParams = M`,
  -- `procBodyContext` alignment): every `M`-key is a `(M ++ O)`-key; no `I`-key is.
  have hIc : ∀ p, List.Mem p (disjointInputs rawInputOnly M) →
      ((ListMap.keys (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M))).contains
        (Prod.fst p)) = false := by
    intro p hp
    have hpI : p.1 ∈ ListMap.keys (disjointInputs rawInputOnly M) := by
      rw [ListMap.keys_eq_map_fst]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem, ListMap_keys_append, List.mem_append]
    rintro (hMk | hOk)
    · exact disjointInputs_key_not_output rawInputOnly M p.1 hpI hMk
    · refine disjointInputs_key_not_output rawOutputOnly (M ++ disjointInputs rawInputOnly M) p.1 hOk ?_
      rw [ListMap_keys_append, List.mem_append]; exact Or.inr hpI
  have hMc : ∀ p, List.Mem p M →
      ((ListMap.keys (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M))).contains
        (Prod.fst p)) = true := by
    intro p hp
    rw [List.contains_iff_mem, ListMap_keys_append, List.mem_append]
    exact Or.inl (by rw [ListMap.keys_eq_map_fst]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
  -- `genLMonoTy` can reach every declared input and output type.
  have key : ∀ (ty : LMonoTy),
      (ty ∈ (M ++ disjointInputs rawInputOnly M).values ∨
       ty ∈ (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)).values) →
      ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) typeArgs size) := by
    intro ty hty
    rcases hty with h | h
    · rw [ListMap_values_append, List.mem_append] at h
      rcases h with h | h
      · exact hMVals ty h
      · exact hRawInVals ty (disjointInputs_values_mem rawInputOnly M ty h)
    · rw [ListMap_values_append, List.mem_append] at h
      rcases h with h | h
      · exact hMVals ty h
      · exact hRawOutVals ty
          (disjointInputs_values_mem rawOutputOnly (M ++ disjointInputs rawInputOnly M) ty h)
  -- The body seed's scope holds nothing but generated signature types, so every one of
  -- them is well-kinded in `C`. This is the scope-local half of `WellKindedOk`, which the
  -- caller therefore does not have to assume.
  have hseedWK : StrataGenerators.Stmt.WellKindedOk octx procs
      { C with rigidTypeVars := typeArgs }
      (M ++ disjointInputs rawInputOnly M ++
        (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) ++ oldVars M) :=
    { hWK typeArgs with
      ctxWK := by
        intro ty hty
        refine genLMonoTy_mem_wellKindedTy (tvars := typeArgs) hC ⟨size, key ty ?_⟩
        rw [Map_values_eq_ListMap_values, ListMap_values_append, ListMap_values_append,
          oldVars_values, List.mem_append, List.mem_append] at hty
        rcases hty with (hMI | hMO) | hM
        · exact Or.inl hMI
        · exact Or.inr hMO
        · exact Or.inl (by rw [ListMap_values_append, List.mem_append]; exact Or.inl hM) }
  -- Body soundness (seeded at `inputs ++ outputs ++ oldVars M`, immutable = inputs.keys ++ old.keys).
  have hbodyTyped : StatementsHasTypeA P { C with rigidTypeVars := typeArgs }
      ((procStmtEnvΓ Γ octx typeArgs pctx).toTCtx
        (M ++ disjointInputs rawInputOnly M ++
          (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) ++ oldVars M)) []
      body C' ((procStmtEnvΓ Γ octx typeArgs pctx).toTCtx ctx') :=
    genStmtChain_sound P (procStmtEnvΓ Γ octx typeArgs pctx)
      (ListMap.keys (M ++ disjointInputs rawInputOnly M) ++ ListMap.keys (oldVars M)) procs
      hProcs []
      { C with rigidTypeVars := typeArgs }
      (M ++ disjointInputs rawInputOnly M ++
        (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) ++ oldVars M)
      hseedWK size len hseedFun (body, C', ctx') hbody
  -- modRights from the sequence invariant (write targets are mutable keys).
  have hmod := genStmtChain_mutableVars octx pctx typeArgs
      (ListMap.keys (M ++ disjointInputs rawInputOnly M) ++ ListMap.keys (oldVars M)) procs []
      { C with rigidTypeVars := typeArgs }
      (M ++ disjointInputs rawInputOnly M ++
        (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) ++ oldVars M)
      size len (body, C', ctx') hbody
  refine {
    inputsNodup := hInputsNodup,
    outputsNodup := hOutputsNodup,
    typeArgsNodup := htyNodup,
    noUndeclaredVars := ?_,
    signatureWellKinded := ?_,
    modRights := ?_,
    preconditionsTyped := ?_,
    postconditionsTyped := ?_,
    bodyTyped := ?_ }
  · -- noUndeclaredVars: every input/output type's ftvars lie in `typeArgs`.
    intro v hv
    have hpiece : ∃ ty, (ty ∈ (M ++ disjointInputs rawInputOnly M).values ∨
          ty ∈ (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)).values)
        ∧ v ∈ LMonoTy.freeVars ty := by
      rcases List.mem_append.mp hv with h | h
      · obtain ⟨ty, hty, hvty⟩ := Freshening.exists_of_freeVars_mem h; exact ⟨ty, Or.inl hty, hvty⟩
      · obtain ⟨ty, hty, hvty⟩ := Freshening.exists_of_freeVars_mem h; exact ⟨ty, Or.inr hty, hvty⟩
    obtain ⟨ty, hty_mem, hv_ty⟩ := hpiece
    have hftv : allFtvarsIn typeArgs ty := genLMonoTy_mem_ftvars (key ty hty_mem)
    exact allFtvarsIn_freeVars hftv v hv_ty
  · -- signatureWellKinded: `tyCompat` is equality at `HasTypeA`, and the generator makes
    -- every declared type. Therefore `hC` gives well-kindedness (`hC` only reads
    -- `knownTypes`, which the `rigidTypeVars` refinement does not touch).
    intro ty hty
    refine ⟨ty, rfl, genLMonoTy_mem_wellKindedTy (tvars := typeArgs) hC ?_⟩
    refine ⟨size, key ty ?_⟩
    rcases List.mem_append.mp hty with h | h
    · exact Or.inl h
    · exact Or.inr h
  · -- modRights: a modified var is a mutable key of the seed `A ++ B ++ C` (with
    -- `A := inputs`, `B := outputs`, `C := oldVars M`), hence — by
    -- `mem_writable_seed_keys` — an *output* key, or a body-defined variable.
    intro v hv
    show v ∈ ListMap.keys (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M))
        ++ HasVarsImp.definedVars (P := Expression) body false
    rcases List.mem_append.mp (hmod.1 v hv) with h | h
    · refine List.mem_append_left _ ?_
      rw [← Map_keys_eq_ListMap_keys]
      refine mem_writable_seed_keys (M ++ disjointInputs rawInputOnly M)
        (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) (oldVars M)
        (ListMap.keys (M ++ disjointInputs rawInputOnly M) ++ ListMap.keys (oldVars M)) ?_ v h
      rw [Map_keys_eq_ListMap_keys, Map_keys_eq_ListMap_keys]
    · exact List.mem_append_right _ h
  · -- preconditionsTyped: under `instHasTypeA` this is `HasTypeA [] c.expr bool`
    -- (the context — hence the clause's free-var context — is ignored by the spec).
    intro c hc
    exact genLExpr_sound _ octx pctx typeArgs [] size .bool _ c.expr
      (genChecks_support _ octx typeArgs size pre pctx hpre c hc)
  · -- postconditionsTyped: identical reduction (the context is ignored).
    intro c hc
    exact genLExpr_sound _ octx pctx typeArgs [] size .bool _ c.expr
      (genChecks_support _ octx typeArgs size post pctx hpost c hc)
  · -- bodyTyped: align the body context via `procBodyContext_inoutΓ`. The two contexts
    -- agree only up to `TContext.Equiv` (opaque hash-map scopes), so the body derivation
    -- is transported along it with `statementsHasTypeA_equiv_congr`.
    refine ProcBodyHasType'.structured body C' ((procStmtEnvΓ Γ octx typeArgs pctx).toTCtx ctx') ?_
    have heq := procBodyContext_inoutΓ Γ hΓtypes name typeArgs M (disjointInputs rawInputOnly M)
      (disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) hIc hMc hseedFun
      pre post (.structured body)
    rw [procStmtEnvΓ_toTCtx] at hbodyTyped
    exact StrataGenerators.Stmt.statementsHasTypeA_equiv_congr hbodyTyped heq

/-- **`ProcBodyHasType'` rigidTypeVars weakening.** Only the `structured` case
    carries a `StatementsHasTypeA` obligation (weakened via `StatementsHasTypeA_weaken_rigid`);
    the `cfg` case is unconstrained. The body-scope `Γ_body` is independent of the
    ambient `C`. -/
theorem ProcBodyHasTypeA_weaken_rigid {P : Program} {C : LContext CoreLParams}
    {Γ_body : TContext Unit} {b : Procedure.Body} {rv : List TyIdentifier}
    (h : ProcBodyHasType' LMonoTy P C Γ_body b) (hsub : rv ⊆ C.rigidTypeVars) :
    ProcBodyHasType' LMonoTy P { C with rigidTypeVars := rv } Γ_body b := by
  cases h with
  | structured ss C'' Γ'' hst =>
    exact ProcBodyHasType'.structured ss { C'' with rigidTypeVars := rv } Γ''
      (StatementsHasTypeA_weaken_rigid hst hsub)
  | cfg c => exact ProcBodyHasType'.cfg c

/-- **Soundness of `genProcedure` at the *ambient* context.** `genProcedure_sound`
    concludes at the `typeArgs`-overridden rigid context (matching
    `Procedure.typeCheck`, which sets `rigidTypeVars` to the type parameters before
    checking the body). But the program-level spec `DeclHasType'.proc` threads the
    ambient `C` *unchanged*. This lemma bridges the two: since the body's
    `StatementsHasTypeA` consumes `C.rigidTypeVars` only through the reflexive-friendly,
    antitone `RigidAnnotCompat` in `init` (and the contract clauses ignore `C`
    entirely under `instHasTypeA`), the conclusion transports down to any rigid set
    `C.rigidTypeVars ⊆ proc.header.typeArgs` — in particular `C`'s own, via
    `StatementsHasTypeA_weaken_rigid`.

    The side-condition `C.rigidTypeVars ⊆ proc.header.typeArgs` holds vacuously when
    the ambient `C.rigidTypeVars = []` (the program-generator fold's invariant), so
    a caller with `hCrigid : C.rigidTypeVars = []` discharges it by
    `hCrigid ▸ List.nil_subset _`. -/
theorem genProcedure_sound_ambient (P : Program) (octx : OpCtx) (procs : ProcSigCtx)
    (hProcs : ProcSigCorresponds procs P) (size len : Nat)
    (C : LContext CoreLParams) (Γ : TContext Unit) (hΓtypes : Γ.types = [])
    (hC : SimpleTyArities C)
    (hWK : ∀ rv : List TyIdentifier,
      StrataGenerators.Stmt.WellKindedAmbient octx procs { C with rigidTypeVars := rv })
    (proc : Procedure) (pctx : PolyOpCtx := [])
    (hproc : proc ∈ SetGen.support
      (genProcedure (G := SetGen.Set) octx procs C Γ size len pctx))
    (hCrigid : C.rigidTypeVars ⊆ proc.header.typeArgs) :
    ProcHasTypeA P C Γ proc := by
  have hbase :=
    genProcedure_sound P octx procs hProcs size len C Γ hΓtypes hC hWK proc pctx hproc
  -- All fields except `bodyTyped` are ambient-`C`-blind (the contract clauses use
  -- `S.exprTyped C … = HasTypeA [] …`, which drops `C`); only `bodyTyped` threads
  -- `C.rigidTypeVars`, and it weakens down to `C`'s own rigid set.
  refine { hbase with bodyTyped := ?_ }
  -- `procBodyContext Γ proc` does not depend on the ambient `C`; the body typing
  -- weakens down to `C`'s own rigid set. Weakening `{ C with rigidTypeVars := typeArgs }`
  -- by `C.rigidTypeVars ⊆ typeArgs` yields the body typed at
  -- `{ { C with rigidTypeVars := typeArgs } with rigidTypeVars := C.rigidTypeVars }`,
  -- which is `C` (structure eta: all fields restored to `C`'s).
  have hsub : C.rigidTypeVars ⊆
      ({ C with rigidTypeVars := proc.header.typeArgs } : LContext CoreLParams).rigidTypeVars :=
    hCrigid
  have hw := ProcBodyHasTypeA_weaken_rigid (rv := C.rigidTypeVars) hbase.bodyTyped hsub
  have hCeq : ({ ({ C with rigidTypeVars := proc.header.typeArgs } : LContext CoreLParams)
      with rigidTypeVars := C.rigidTypeVars } : LContext CoreLParams) = C := rfl
  rw [hCeq] at hw
  exact hw

-- ── Completeness ─────────────────────────────────────────────────────────

set_option maxHeartbeats 800000 in
/-- **Completeness of `genProcedure`.** Every procedure whose signature admits the
    generator's three-block decomposition — `inputs = M ++ I`,
    `outputs = M ++ O` with `M` (in-out) shared and leading both, `I` (input-only)
    key-disjoint from `M`, and `O` (output-only) key-disjoint from `M ++ I` — and
    (a) has the default
    values for the fields the generator does not vary (`noFilter := false`, a
    *structured* body) and (b) whose name, type arguments, each of the three
    signature blocks, contract, and body are individually reachable by the
    corresponding sub-generators, is in `genProcedure`'s support.

    The three-block disjointness hypotheses (`hIdisjM`, `hOdisjMI`) are the
    completeness-only side-conditions witnessing that the generator's
    `disjointInputs` filters reproduce `I` and `O` unchanged (idempotence, via
    `disjointInputs_eq_self`). The `procs : ProcSigCtx` here is the same call-target
    context `genProcedure` threads into the body; `hBodyReach` is stated against it,
    and `genProcedure_sound`'s only side-condition is the matching
    `ProcSigCorresponds procs P` that certifies those targets against `P`.

    - `hInputsEq` / `hOutputsEq` — the three-block decomposition of the signature
      (shared block `M` leading both);
    - `hName` — the procedure name is a reachable identifier string;
    - `hTyArgsLen` / `hTyArgsReach` — the (already `Nodup`) type arguments are no
      longer than `size` and each is reachable by `genIdentName`;
    - `hM*` / `hI*` / `hO*` — for each block: `Nodup` keys, a length bound and
      per-name `genIdentName` reachability of the key names, and per-value
      `genLMonoTy` reachability;
    - `hPre*` / `hPost*` — each contract clause is default-`attr`/empty-`md`, its
      label list is reachable by `genNameList`, and its `expr` is reachable by
      `genLExpr … .bool`;
    - `hBodyReach` — the body statement list is in `genStmtChain`'s support, seeded
      exactly as the generator seeds it (`M ++ I ++ (M ++ O) ++ oldVars M`, immutable
      names `keys (M ++ I) ++ keys (oldVars M)`), at empty label/fvar contexts,
      type-variable list `typeArgs`, and the rigidified ambient `C`. (A caller can
      obtain this membership from `spec_complete` applied to each body statement.)

    The block name-length / reachability conditions are stated concretely via
    `mem_support_genNameList_iff`. -/
theorem genProcedure_complete (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (Γ : TContext Unit) (size len : Nat)
    (proc : Procedure)
    (M I O : ListMap (Identifier Unit) LMonoTy)
    (bodyss : List Statement) (C' : LContext CoreLParams) (ctx' : VarCtx)
    -- the generator does not vary these fields, so they must be at defaults:
    (hNoFilter : proc.header.noFilter = false)
    (hBodyEq : proc.body = .structured bodyss)
    -- three-block decomposition (shared block `M` leading both):
    (hInputsEq : proc.header.inputs = M ++ I)
    (hOutputsEq : proc.header.outputs = M ++ O)
    (hIdisjM : ∀ k ∈ ListMap.keys I, k ∉ ListMap.keys M)
    (hOdisjMI : ∀ k ∈ ListMap.keys O, k ∉ ListMap.keys (M ++ I))
    -- name / typeArgs reachability:
    (hName : proc.header.name.name ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hTyArgsNodup : proc.header.typeArgs.Nodup)
    (hTyArgsLen : proc.header.typeArgs.length ≤ size)
    (hTyArgsReach : ∀ s ∈ proc.header.typeArgs, s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    -- in-out block `M` reachability:
    (hMNodup : M.keys.Nodup)
    (hMNamesLen : (M.keys.map (·.name)).length ≤ size)
    (hMNamesReach : ∀ s ∈ M.keys.map (·.name), s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hMTyReach : ∀ ty ∈ M.values,
      ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) proc.header.typeArgs size))
    -- input-only block `I` reachability:
    (hINodup : I.keys.Nodup)
    (hINamesLen : (I.keys.map (·.name)).length ≤ size)
    (hINamesReach : ∀ s ∈ I.keys.map (·.name), s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hITyReach : ∀ ty ∈ I.values,
      ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) proc.header.typeArgs size))
    -- output-only block `O` reachability:
    (hONodup : O.keys.Nodup)
    (hONamesLen : (O.keys.map (·.name)).length ≤ size)
    (hONamesReach : ∀ s ∈ O.keys.map (·.name), s ∈ SetGen.support (genIdentName (G := SetGen.Set)))
    (hOTyReach : ∀ ty ∈ O.values,
      ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) proc.header.typeArgs size))
    -- preconditions:
    (hPreLabels : proc.spec.preconditions.keys ∈ SetGen.support (genNameList (G := SetGen.Set) size))
    (hPreAttr : ∀ c ∈ proc.spec.preconditions.values, c.attr = .Default)
    (hPreMd : ∀ c ∈ proc.spec.preconditions.values, c.md = #[])
    (hPreExpr : ∀ c ∈ proc.spec.preconditions.values,
      c.expr ∈ SetGen.support (genLExpr (G := SetGen.Set)
        (sigFctx (M ++ I)) octx [] proc.header.typeArgs [] size .bool))
    -- postconditions:
    (hPostLabels : proc.spec.postconditions.keys ∈ SetGen.support (genNameList (G := SetGen.Set) size))
    (hPostAttr : ∀ c ∈ proc.spec.postconditions.values, c.attr = .Default)
    (hPostMd : ∀ c ∈ proc.spec.postconditions.values, c.md = #[])
    (hPostExpr : ∀ c ∈ proc.spec.postconditions.values,
      c.expr ∈ SetGen.support (genLExpr (G := SetGen.Set)
        (sigFctx (M ++ I ++ (M ++ O) ++ oldVars M)) octx [] proc.header.typeArgs [] size .bool))
    (hBodyReach : (bodyss, C', ctx') ∈ SetGen.support
      (genStmtChain (G := SetGen.Set) octx proc.header.typeArgs
        (ListMap.keys (M ++ I) ++ ListMap.keys (oldVars M)) procs []
        { C with rigidTypeVars := proc.header.typeArgs }
        (M ++ I ++ (M ++ O) ++ oldVars M) [] size len)) :
    proc ∈ SetGen.support (genProcedure (G := SetGen.Set) octx procs C Γ size len) := by
  simp only [genProcedure, mem_support_bind_iff, mem_support_pure_iff]
  -- The generator's `disjointInputs` filters reproduce `I` and `O` unchanged.
  have hI_eq : disjointInputs I M = I := disjointInputs_eq_self I M hIdisjM
  have hO_eq : disjointInputs O (M ++ I) = O := disjointInputs_eq_self O (M ++ I) hOdisjMI
  -- Witnesses: name, type args, the three blocks `M`/`I`/`O`, contracts, body triple.
  refine ⟨proc.header.name.name, hName,
          proc.header.typeArgs, ?_,
          M, ?_,
          I, ?_,
          O, ?_,
          proc.spec.preconditions, ?_,
          proc.spec.postconditions, ?_,
          (bodyss, C', ctx'), ?_, ?_⟩
  · exact genTypeArgs_complete size proc.header.typeArgs hTyArgsNodup
      (mem_support_genNameList_iff size _ |>.mpr ⟨hTyArgsLen, hTyArgsReach⟩)
  · exact genInputs_complete proc.header.typeArgs size M hMNodup
      (mem_support_genNameList_iff size _ |>.mpr ⟨hMNamesLen, hMNamesReach⟩) hMTyReach
  · exact genInputs_complete proc.header.typeArgs size I hINodup
      (mem_support_genNameList_iff size _ |>.mpr ⟨hINamesLen, hINamesReach⟩) hITyReach
  · exact genInputs_complete proc.header.typeArgs size O hONodup
      (mem_support_genNameList_iff size _ |>.mpr ⟨hONamesLen, hONamesReach⟩) hOTyReach
  · rw [hI_eq]
    exact genChecks_complete (sigFctx (M ++ I))
      octx proc.header.typeArgs size proc.spec.preconditions
      hPreLabels hPreAttr hPreMd hPreExpr
  · rw [hI_eq, hO_eq]
    exact genChecks_complete (sigFctx (M ++ I ++ (M ++ O) ++ oldVars M))
      octx proc.header.typeArgs size proc.spec.postconditions
      hPostLabels hPostAttr hPostMd hPostExpr
  · -- body reachable: the generator's filtered blocks equal `I`/`O`; `hBodyReach`
    -- is the body's `genStmtChain` support membership directly.
    rw [hI_eq, hO_eq]
    exact hBodyReach
  · -- the reassembled record equals `proc`.
    rw [hI_eq, hO_eq]
    obtain ⟨⟨pname, ptyArgs, pinputs, poutputs, pnoFilter⟩, ⟨ppre, ppost⟩, pbody⟩ := proc
    obtain ⟨nm, nmeta⟩ := pname
    simp only at hInputsEq hOutputsEq hNoFilter hBodyEq ⊢
    subst hNoFilter hBodyEq hInputsEq hOutputsEq
    rfl

end StrataGenerators.Procedure
