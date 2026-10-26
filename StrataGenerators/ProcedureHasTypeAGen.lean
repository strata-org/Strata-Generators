import StrataGenerators.ProcedureHasTypeAGen.Core
import StrataGenerators.ProcedureHasTypeAGen.Support
import StrataGenerators.ProcedureHasTypeAGen.MutableVars
import StrataGenerators.CmdHasTypeAGenSound
import Strata.Languages.Core.ProcedureTypeSpec
import Strata.Languages.Core.TypingSpec

open Lambda LExpr RandomChoice Core Imperative TypeSpec SetGen
open StrataGenerators.Stmt StrataGenerators.Function
open StrataGenerators.AnnotFacts (genLExpr_exprWellTyped)

/-!
# Soundness and completeness of `genProcedure`

`genProcedure` (in `ProcedureHasTypeAGen/Core.lean`) generates well-typed Strata
Core procedures. This file proves it **sound** and **complete** with respect to
the `ProcHasTypeA` typing relation of `Strata.Languages.Core.ProcedureTypeSpec`.

The proof is *compositional*: it reuses `genInputs_support`/`genInputs_complete`
for the output signature, exactly as the generator of a function uses them for its inputs. It also uses
`genStmtChain_sound` and the membership of the body in the support of `genStmtChain`, for the body. The
completeness proof takes that membership as a hypothesis, and `spec_complete` can discharge it. It also uses
`genStmtChain_mutableVars`, for the obligation about the rights to modify a variable.

## The context-alignment lemma

The one genuinely procedure-specific fact is `procBodyContext_default`: with
empty inputs, empty type-arguments, and no in-out parameters, the declarative
body context `procBodyContext Γ proc` (a single new scope binding inputs ++
outputs and the old bindings, becomes `procToTCtx proc.header.outputs`. That is exactly the context that
`genStmtChain_sound` gives when it starts from the output parameters. That fact is what makes the
`StatementsHasTypeA` of the generated body agree *definitionally* with the
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

/-- `ListMap.keys` distributes over the append of two `ListMap` values, and that append is `List.append`. The
    `++` of a `ListMap` is not *syntactically* `List.append`, so `List.map_append` does not apply directly. The
    proof therefore goes through the bridge lemma about `Map.keys`. -/
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
theorem getInoutParams_inout (name : String) (tyArgs : List TyIdentifier) {lemmas : List String}
    (M I O : List ((Identifier Unit) × LMonoTy))
    (hI : ∀ p ∈ I, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = false)
    (hM : ∀ p ∈ M, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = true) :
    ({ name := ⟨name, ()⟩, typeArgs := tyArgs, inputs := M ++ I, outputs := M ++ O,
       lemmas := lemmas } : Procedure.Header).getInoutParams = M := by
  simp only [Procedure.Header.getInoutParams]
  show List.filter _ (M ++ I) = M
  have hInil : List.filter (fun p => (ListMap.keys (M ++ O)).contains p.1) I = [] :=
    List.filter_eq_nil_iff.mpr (fun p hp hpt => Bool.false_ne_true ((hI p hp).symm.trans hpt))
  rw [List.filter_append, List.filter_eq_self.mpr hM, hInil]
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
    of the specification, which is `old ++ outputs ++ inputs`, and the one of the generator, which is
    `(inputs ++ outputs ++ old).reverse`, are functional permutations of each other. They hold the same bindings
    in a different order, so a lookup in one gives the same value as a lookup in the other, and that is all that
    `TContext.Equiv` asks for. A structural equality is not available, because a scope is a hash map, and two
    hash maps that different orders of insertion build are different values. -/
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

/-- Mapping over an appended `ListMap` maps each part. -/
theorem listMap_map_append {α β γ : Type} (f : α × β → γ) (l₁ l₂ : ListMap α β) :
    List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂ :=
  List.map_append

/-- **Context alignment (in-out), Γ-parameterized.** For the three-block layout (shared
    block `M` leading both signatures) over an ambient type-scope `Γ` with `Γ.types = []`,
    the declarative body context `procBodyContext Γ proc` agrees with the single-scope
    `procToTCtxΓ Γ (inputs ++ outputs ++ oldVars M)`.

    Agreement is `TContext.Equiv`, not equality: `procBodyContext` builds its scope as
    `HMap.ofList (old ++ outputs ++ inputs)`, and `procToTCtxΓ` builds
    `HMap.ofList ((inputs ++ outputs ++ old).reverse)`. Those hold the same bindings in a different order.
    Therefore a *lookup* in one gives the same value as a lookup in the other, because the seed is functional,
    and the two hash-map values differ. The hypothesis `hfun` gives that functionality, and `seed_functional`
    gives it at a call site. -/
theorem procBodyContext_inoutΓ (Γ : TContext Unit) (hΓtypes : Γ.types = [])
    (name : String) (tyArgs : List TyIdentifier) {lemmas : List String}
    (M I O : List ((Identifier Unit) × LMonoTy))
    (hI : ∀ p ∈ I, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = false)
    (hM : ∀ p ∈ M, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = true)
    (hfun : Map.Functional
      (M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))))
    (pre post : ListMap CoreLabel Procedure.Check) (body : Procedure.Body) :
    TContext.Equiv (T := CoreLParams)
      (procBodyContext Γ
        { header := { name := ⟨name, ()⟩, typeArgs := tyArgs, inputs := M ++ I,
                      outputs := M ++ O, lemmas := lemmas },
          spec := { preconditions := pre, postconditions := post },
          body := body })
      (procToTCtxΓ Γ (M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2)))) := by
  -- Write the two scopes out. The specification builds `old ++ outputs ++ inputs`, and the generator builds the
  -- reverse of `inputs ++ outputs ++ old`. This file uses no set type, so each block appears in full.
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
                      outputs := M ++ O, lemmas := lemmas },
          spec := { preconditions := pre, postconditions := post },
          body := body }).types
      = [Strata.Util.HMap.ofList
          ((M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))).map
                (fun p => (p.1, LTy.forAll [] p.2))
            ++ (M ++ O).map (fun p => (p.1, LTy.forAll [] p.2))
            ++ (M ++ I).map (fun p => (p.1, LTy.forAll [] p.2)))] from by
    simp only [procBodyContext, procBodyScopes, hΓtypes, Strata.Util.HMaps.push, formalsScope,
      getInoutParams_inout name tyArgs M I O hI hM, listMap_map_append, List.map_append,
      List.map_map, Function.comp_def]]
  rw [show (procToTCtxΓ Γ
        (M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2)))).types
      = [Strata.Util.HMap.ofList
          (((M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))).map
            (fun p => (p.1, LTy.forAll [] p.2))).reverse)] from rfl]
  exact ⟨fun k => (find?_ofList_perm_of_functional hperm hfun' k).symm, True.intro⟩

/-- **Context alignment (in-out).** The `default`-ambient special case of
    `procBodyContext_inoutΓ` (`default.types = []`). -/
theorem procBodyContext_inout (name : String) (tyArgs : List TyIdentifier) {lemmas : List String}
    (M I O : List ((Identifier Unit) × LMonoTy))
    (hI : ∀ p ∈ I, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = false)
    (hM : ∀ p ∈ M, ((ListMap.keys (M ++ O)).contains (Prod.fst p)) = true)
    (hfun : Map.Functional
      (M ++ I ++ (M ++ O) ++ M.map (fun p => (CoreIdent.mkOld p.1.name, p.2))))
    (pre post : ListMap CoreLabel Procedure.Check) (body : Procedure.Body) :
    TContext.Equiv (T := CoreLParams)
      (procBodyContext (default)
        { header := { name := ⟨name, ()⟩, typeArgs := tyArgs, inputs := M ++ I,
                      outputs := M ++ O, lemmas := lemmas },
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

/-- `disjointInputs ins outs` is a *sublist* of `ins`, because it removes an entry only. Therefore each property
    that is closed under a sublist holds for it if it holds for `ins`. Two such properties are that the keys are
    distinct, and that each value is reachable. -/
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
    leaves exactly the output keys. That fact is what turns the invariant of `genStmtChain_mutableVars`, which
    is about the writable part of a context, into the obligation `ProcHasType'.modRights`, and it needs **no**
    hypothesis about disjointness. -/
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
    a key of the *middle* block `B`. A mutable key is a key of `A ++ B ++ C` that is neither a key of `A` nor a
    key of `C`, because both of those blocks are immutable, so it must be a key of `B`. At the instance where
    `A` is the inputs, `B` is the outputs and `C` is the old variables, this lemma says that each variable that
    the body modifies is an *output* key, and it therefore discharges `modRights`. No
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

/-- Two maps whose *keys* come from disjoint classes of characters share no key. One class holds no space, and
    the other holds a space in each name. Therefore the append of the two maps is functional whenever each half
    is functional. That is how the map of the old variables, whose keys hold a space, composes with the
    generated signature, whose keys hold no space. -/
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
    have distinct keys, and each of them is therefore functional. They also agree at a shared key. A key of both
    halves is not a key of the input-only block, which is disjoint from the outputs, and it is not a key of the
    output-only block, which is disjoint from the inputs. Therefore both entries come from the shared block
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
    is in the support of `genLExpr … .bool`. -/
theorem mapM_genChecks_values (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) (depth : Nat)
    (labels : List CoreLabel) (m : ListMap CoreLabel Procedure.Check) (pctx : PolyOpCtx := [])
    (hm : m ∈ SetGen.support
      (labels.mapM (m := SetGen.Set) (fun l => do
        let e ← genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth .bool
        pure (l, ({ expr := e } : Procedure.Check))))) :
    ∀ c ∈ m.values,
      c.expr ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth .bool) := by
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

/-- Membership in `genChecks octx tvars depth`: every clause's `expr` is a `bool` expression
    reachable by `genLExpr`. -/
theorem genChecks_support (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap CoreLabel Procedure.Check) (pctx : PolyOpCtx := [])
    (hm : m ∈ SetGen.support (genChecks (G := SetGen.Set) fctx octx tvars depth pctx)) :
    ∀ c ∈ m.values,
      c.expr ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx pctx tvars [] depth .bool) := by
  simp only [genChecks, mem_support_bind_iff] at hm
  obtain ⟨labels, _, hm⟩ := hm
  exact mapM_genChecks_values fctx octx tvars depth labels m pctx hm

/-- Reverse of `mapM_genChecks_values`: a `ListMap` of checks whose every `expr`
    is reachable by `genLExpr … .bool` is in the support
    of the `mapM` inside `genChecks`, run over its own keys. -/
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
    -- The head check `{ expr := c.expr }` equals `c`, since `c`'s
    -- `attr`/`md` are at defaults.
    have hc_eq : ({ expr := c.expr } : Procedure.Check) = c := by
      have ha := hattr _ hc_mem
      have hmm := hmd _ hc_mem
      cases c with
      | mk e a md => subst ha; subst hmm; rfl
    -- Witness the actual head pair `(l, c)`; its membership in the generator's
    -- head step holds because `pure` produces `(l, { expr := c.expr }) = (l, c)`.
    refine ⟨(l, c), ⟨c.expr, hce, ?_⟩, rest, ih hrest_attr hrest_md hrest, rfl⟩
    show (l, c) ∈ SetGen.support
      (pure (l, ({ expr := c.expr } : Procedure.Check)) : SetGen.Set _)
    rw [mem_support_pure_iff, hc_eq]

/-- Completeness of `genChecks`: a check `ListMap` whose labels' names are
    reachable by `genNameList`, whose clauses are all default-`attr`/empty-`md`,
    and whose every `expr` is reachable by `genLExpr … .bool`, is in the support of
    `genChecks`. -/
theorem genChecks_complete (fctx : FVarCtx) (octx : OpCtx) (tvars : List TyIdentifier) (depth : Nat)
    (m : ListMap CoreLabel Procedure.Check)
    (hlabels : m.keys ∈ SetGen.support (genNameList (G := SetGen.Set) depth))
    (hattr : ∀ c ∈ m.values, c.attr = .Default)
    (hmd : ∀ c ∈ m.values, c.md = #[])
    (hvals : ∀ c ∈ m.values, c.expr ∈ SetGen.support (genLExpr (G := SetGen.Set) fctx octx [] tvars [] depth .bool)) :
    m ∈ SetGen.support (genChecks (G := SetGen.Set) fctx octx tvars depth) := by
  simp only [genChecks, mem_support_bind_iff]
  exact ⟨m.keys, hlabels, mapM_genChecks_complete fctx octx tvars depth m hattr hmd hvals⟩

-- ── Context irrelevance of function typing ───────────────────────────────

-- ── Formal parameters avoid function names ───────────────────────────────

/-- A signature drawn by `genInputs` without the parameters named after a function of `C` has
    distinct keys, types that `genLMonoTy` reaches, keys without a space, and no key named after a
    function of `C`. -/
theorem avoidFunctionNames_support (C : LContext CoreLParams) (tvars : List TyIdentifier)
    (size : Nat) (raw : ListMap (Identifier Unit) LMonoTy)
    (hraw : raw ∈ SetGen.support
      (genInputs (G := SetGen.Set) (genLMonoTy (G := SetGen.Set) tvars size) size)) :
    (ListMap.keys (avoidFunctionNames C raw)).Nodup ∧
    (∀ ty ∈ (avoidFunctionNames C raw).values,
      ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) tvars size)) ∧
    (∀ k ∈ ListMap.keys (avoidFunctionNames C raw), ' ' ∉ k.name.toList) ∧
    (∀ k ∈ ListMap.keys (avoidFunctionNames C raw), k.name ∉ C.functions) := by
  obtain ⟨hnodup, hvals⟩ := genInputs_support _ size raw hraw
  refine ⟨keys_filter_nodup _ raw hnodup,
    fun ty hty => hvals ty (ListMap.mem_values_filter _ raw ty hty), ?_, ?_⟩
  · intro k hk
    obtain ⟨y, hmem, _⟩ := mem_keys_filter _ raw k hk
    have hkraw : k ∈ ListMap.keys raw := by
      rw [ListMap.keys_eq_map_fst]; exact List.mem_map.mpr ⟨(k, y), hmem, rfl⟩
    exact genInputs_key_no_space _ size raw hraw k hkraw
  · intro k hk hfn
    obtain ⟨y, _, hkeep⟩ := mem_keys_filter _ raw k hk
    have hin : (functionNames C).contains k.name = true :=
      List.contains_iff_mem.mpr (mem_functionNames hfn)
    simp only [hin, Bool.not_true] at hkeep
    exact Bool.false_ne_true hkeep

/-- A signature with no key named after a function of `C` is unchanged by
    `avoidFunctionNames`. -/
theorem avoidFunctionNames_eq_self (C : LContext CoreLParams)
    (sig : ListMap (Identifier Unit) LMonoTy)
    (h : ∀ k ∈ ListMap.keys sig, k.name ∉ C.functions) : avoidFunctionNames C sig = sig := by
  simp only [avoidFunctionNames]
  apply List.filter_eq_self.mpr
  intro p hp
  have hk : p.1 ∈ ListMap.keys sig := by
    rw [ListMap.keys_eq_map_fst]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hnot : (functionNames C).contains p.1.name = false := by
    rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
    exact fun hmem => h p.1 hk (mem_functions_of_mem_functionNames hmem)
  simp only [hnot, Bool.not_false]

-- ── Soundness ────────────────────────────────────────────────────────────

/-- The scope of the generator for a signature with distinct keys agrees on every lookup with the
    single scope that binds each entry of the signature at its type. -/
theorem procToTCtx_find_eq_ofList (sig : ListMap (Identifier Unit) LMonoTy)
    (hnd : (Map.keys sig).Nodup) (k : Identifier Unit) :
    (procToTCtx sig).types.find? k =
      Strata.Util.HMaps.find?
        [Strata.Util.HMap.ofList (sig.map (fun p => (p.1, LTy.forAll [] p.2)))] k := by
  have hfun := Map.functional_of_nodup sig hnd
  show Strata.Util.HMaps.find? [_] k = _
  rw [Strata.Util.HMaps.find?_single_scope, Strata.Util.HMaps.find?_single_scope]
  refine find?_ofList_perm_of_functional (List.reverse_perm _) ?_ k
  intro x v1 v2 h1 h2
  rw [List.mem_reverse] at h1 h2
  obtain ⟨p1, hp1, hpe1⟩ := List.mem_map.mp h1
  obtain ⟨p2, hp2, hpe2⟩ := List.mem_map.mp h2
  simp only [Prod.mk.injEq] at hpe1 hpe2
  obtain ⟨hk1, hv1⟩ := hpe1
  obtain ⟨hk2, hv2⟩ := hpe2
  rw [← hv1, ← hv2, hfun x p1.2 p2.2 (by rw [← hk1]; exact hp1) (by rw [← hk2]; exact hp2)]

/-- The outputs of a procedure that `genProcedure` draws have distinct names: the in-out block and
    the output-only block each have distinct names, and the output-only block avoids the in-out
    names. -/
theorem genProcedure_outputs_nodup {octx : OpCtx} {procs : ProcSigCtx} {C : LContext CoreLParams}
    {Γ : TContext Unit} {size len : Nat} {pctx : PolyOpCtx} {proc : Procedure}
    (hproc : proc ∈ SetGen.support
      (genProcedure (G := SetGen.Set) octx procs C Γ size len pctx)) :
    (ListMap.keys proc.header.outputs).Nodup := by
  simp only [genProcedure, genProcedureWith, mem_support_bind_iff, mem_support_pure_iff] at hproc
  obtain ⟨_, _, typeArgs, _, rawM, hrawM, rawIn, _, rawOut, hrawOut, _, _, _, _, _, _, _, _,
    rfl⟩ := hproc
  show (ListMap.keys (avoidFunctionNames C rawM ++ disjointInputs (avoidFunctionNames C rawOut)
    (avoidFunctionNames C rawM ++ disjointInputs (avoidFunctionNames C rawIn)
      (avoidFunctionNames C rawM)))).Nodup
  rw [ListMap_keys_append, List.nodup_append]
  refine ⟨(avoidFunctionNames_support C typeArgs size rawM hrawM).1,
    disjointInputs_keys_nodup _ _ (avoidFunctionNames_support C typeArgs size rawOut hrawOut).1, ?_⟩
  intro a ha b hb hab
  refine disjointInputs_key_not_output _ _ b hb ?_
  rw [ListMap_keys_append, List.mem_append]
  exact Or.inl (hab ▸ ha)

set_option maxHeartbeats 800000 in
/-- **Soundness of `genProcedure`.** Every procedure in the generator's support is well-typed
    (`ProcWellTyped`) in context `C` with no enclosing variable scope, for any program `P` whose
    callable procedures the call-target context `procs` describes (`ProcSigCorresponds`) and
    whose type names are not local type names (`isLocalTypeName`). This
    holds when the operators and schemes the expressions draw on agree with `C` (`ExprCtxOk`), and
    the operator types and the written-to blocks of the callees are well kinded in `C` at every
    list of rigid type variables (`WellKindedAmbient`).

    The body is typed from the generator's seed of inputs, outputs and `old` bindings, whose
    scope agrees with the procedure's body scopes on every lookup. -/
theorem genProcedure_sound (P : Program) (octx : OpCtx) (procs : ProcSigCtx)
    (hProcs : ProcSigCorresponds procs P)
    (hLocalTypes : ∀ n ∈ programNamesOfKind P .type, ¬ isLocalTypeName n.name)
    (size len : Nat) (C : LContext CoreLParams) (Γ : TContext Unit)
    (hWK : ∀ rv : List TyIdentifier,
      StrataGenerators.Stmt.WellKindedAmbient octx procs { C with rigidTypeVars := rv })
    (pctx : PolyOpCtx) (hops : StrataGenerators.AnnotFacts.ExprCtxOk C [] [] octx pctx)
    (proc : Procedure)
    (hproc : proc ∈ SetGen.support
      (genProcedure (G := SetGen.Set) octx procs C Γ size len pctx)) :
    ProcWellTyped P C [] proc := by
  have hOutputsNodup := genProcedure_outputs_nodup hproc
  simp only [genProcedure, genProcedureWith, mem_support_bind_iff, mem_support_pure_iff] at hproc
  obtain ⟨name, _, typeArgs, htypeArgs, rawM, hrawM, rawIn, hrawIn,
          rawOut, hrawOut, pre, hpre, post, hpost,
          ⟨body, C', ctx'⟩, hbody, lemmas, _, rfl⟩ := hproc
  -- The three blocks without the function names: `M` (in-out), `rawInputOnly` and
  -- `rawOutputOnly`, before the disjointness filters.
  obtain ⟨hMKeysNodup, hMVals, hMs0, _⟩ := avoidFunctionNames_support C typeArgs size rawM hrawM
  obtain ⟨hRawInKeysNodup, hRawInVals, hRawIns, _⟩ :=
    avoidFunctionNames_support C typeArgs size rawIn hrawIn
  obtain ⟨_, hRawOutVals, hRawOuts, _⟩ := avoidFunctionNames_support C typeArgs size rawOut hrawOut
  generalize avoidFunctionNames C rawM = M
    at hMKeysNodup hMVals hMs0 hOutputsNodup hpre hpost hbody ⊢
  generalize avoidFunctionNames C rawIn = rawInputOnly
    at hRawInKeysNodup hRawInVals hRawIns hOutputsNodup hpre hpost hbody ⊢
  generalize avoidFunctionNames C rawOut = rawOutputOnly
    at hRawOutVals hRawOuts hOutputsNodup hpost hbody ⊢
  -- The derived blocks `I := disjointInputs rawInputOnly M` and
  -- `O := disjointInputs rawOutputOnly (M ++ I)` appear in full below.
  have htyNodup : typeArgs.Nodup := genTypeArgs_nodup size typeArgs htypeArgs
  have hIKeysNodup : (ListMap.keys (disjointInputs rawInputOnly M)).Nodup :=
    disjointInputs_keys_nodup rawInputOnly M hRawInKeysNodup
  -- `inputsNodup`: an append of two disjoint `Nodup` blocks.
  have hInputsNodup : (ListMap.keys (M ++ disjointInputs rawInputOnly M)).Nodup := by
    rw [ListMap_keys_append, List.nodup_append]
    refine ⟨hMKeysNodup, hIKeysNodup, ?_⟩
    intro a ha b hb hab
    exact disjointInputs_key_not_output rawInputOnly M b hb (hab ▸ ha)
  -- Space-freeness of the three blocks' keys (generated names have no space).
  have hMs : ∀ k ∈ Map.keys M, ' ' ∉ k.name.toList := by
    intro k hk; rw [Map_keys_eq_ListMap_keys] at hk
    exact hMs0 k hk
  have hIs : ∀ k ∈ Map.keys (disjointInputs rawInputOnly M), ' ' ∉ k.name.toList := by
    intro k hk; rw [Map_keys_eq_ListMap_keys] at hk
    exact hRawIns k ((disjointInputs_keys_sublist rawInputOnly M).subset hk)
  have hOs : ∀ k ∈ Map.keys (disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)),
      ' ' ∉ k.name.toList := by
    intro k hk; rw [Map_keys_eq_ListMap_keys] at hk
    exact hRawOuts k
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
  -- The body seed's scope holds nothing but generated signature types.
  have hseedVals : ∀ ty ∈ Map.values
      (M ++ disjointInputs rawInputOnly M ++
        (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) ++ oldVars M),
      ty ∈ SetGen.support (genLMonoTy (G := SetGen.Set) typeArgs size) := by
    intro ty hty
    refine key ty ?_
    rw [Map_values_eq_ListMap_values, ListMap_values_append, ListMap_values_append,
      oldVars_values, List.mem_append, List.mem_append] at hty
    rcases hty with (hMI | hMO) | hM
    · exact Or.inl hMI
    · exact Or.inr hMO
    · exact Or.inl (by rw [ListMap_values_append, List.mem_append]; exact Or.inl hM)
  have hseedTyWK : ∀ ty ∈ Map.values
      (M ++ disjointInputs rawInputOnly M ++
        (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) ++ oldVars M),
      C.WellKindedTy ty :=
    fun ty hty =>
      genLMonoTy_mem_wellKindedTy (tvars := typeArgs) hops.arities ⟨size, hseedVals ty hty⟩
  -- So every seed type is well-kinded in `C`: the scope-local half of `WellKindedOk`.
  have hseedWK : StrataGenerators.Stmt.WellKindedOk octx procs
      { C with rigidTypeVars := C.rigidTypeVars ++ typeArgs }
      (M ++ disjointInputs rawInputOnly M ++
        (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) ++ oldVars M) :=
    { hWK (C.rigidTypeVars ++ typeArgs) with ctxWK := hseedTyWK }
  -- Body soundness (seeded at `inputs ++ outputs ++ oldVars M`, immutable = inputs.keys ++ old.keys).
  have hbodyTyped : StatementsWellTyped P { C with rigidTypeVars := C.rigidTypeVars ++ typeArgs }
      (procToTCtx
        (M ++ disjointInputs rawInputOnly M ++
          (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) ++
            oldVars M)).types []
      body C' (procToTCtx ctx').types :=
    genStmtChain_sound P (procStmtEnv octx typeArgs pctx)
      (ListMap.keys (M ++ disjointInputs rawInputOnly M) ++ ListMap.keys (oldVars M)) procs
      hProcs hLocalTypes []
      { C with rigidTypeVars := C.rigidTypeVars ++ typeArgs }
      (M ++ disjointInputs rawInputOnly M ++
        (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) ++ oldVars M)
      hseedWK (hops.mono rfl (fun _ _ hv => hv)) size len hseedFun (body, C', ctx') hbody
  -- modRights from the sequence invariant (write targets are mutable keys).
  have hmod := genStmtChain_mutableVars octx pctx typeArgs
      (ListMap.keys (M ++ disjointInputs rawInputOnly M) ++ ListMap.keys (oldVars M)) procs []
      { C with rigidTypeVars := C.rigidTypeVars ++ typeArgs }
      (M ++ disjointInputs rawInputOnly M ++
        (M ++ disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) ++ oldVars M)
      size len (body, C', ctx') hbody
  -- The body scopes of the procedure agree with the scope of the seed on every lookup.
  have heq := procBodyContext_inout name typeArgs (lemmas := lemmas) M
    (disjointInputs rawInputOnly M)
    (disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) hIc hMc hseedFun
    pre post (.structured body)
  -- A contract clause drawn over a scope `ctx` is well-typed at `bool` in every variable
  -- scopes that bind each name of `ctx` at its type.
  have hcheck : ∀ (ctx : VarCtx) (ts : TypeScopes) (m : ListMap CoreLabel Procedure.Check),
      Map.Functional ctx → (∀ ty ∈ ctx.values, C.WellKindedTy ty) →
      (∀ x v, (procToTCtx ctx).types.find? x = some v → ts.find? x = some v) →
      m ∈ SetGen.support (genChecks (G := SetGen.Set) (sigFctx ctx) octx typeArgs size pctx) →
      ∀ c ∈ m.values, ExprWellTyped C ts c.expr .bool := by
    intro ctx ts m hfun hwk hts hm c hc
    have he := genChecks_support (sigFctx ctx) octx typeArgs size m pctx hm c hc
    exact exprWellTyped_mono
      (genLExpr_exprWellTyped (exprCtxOk_of_corresponds hops (procToTCtx_corr ctx) hfun hwk)
        (knownInstance_bool hops.arities) he) hts
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
  · -- signatureWellKinded: the generator makes every declared type.
    intro ty hty
    refine genLMonoTy_mem_wellKindedTy (tvars := typeArgs) hops.arities ⟨size, key ty ?_⟩
    rcases List.mem_append.mp hty with h | h
    · exact Or.inl h
    · exact Or.inr h
  · -- A modified variable is a mutable key of the seed, which is the inputs, then the outputs,
    -- then the old variables. Therefore `mem_writable_seed_keys` makes it an *output* key, or the
    -- body defines it.
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
  · -- preconditions: drawn over the inputs, whose scope agrees with the input scopes.
    refine hcheck _ _ pre (Map.functional_of_nodup _ hInNodup') ?_ ?_ hpre
    · intro ty hty
      refine genLMonoTy_mem_wellKindedTy (tvars := typeArgs) hops.arities ⟨size, key ty ?_⟩
      rw [Map_values_eq_ListMap_values] at hty
      exact Or.inl hty
    · intro x v hx
      rw [procToTCtx_find_eq_ofList _ hInNodup' x] at hx
      exact hx
  · -- postconditions: drawn over the seed, whose scope agrees with the body scopes.
    exact hcheck _ _ post hseedFun hseedTyWK
      (fun x _ hx => (Strata.Util.HMaps.Equiv.find? heq.1 x).trans hx) hpost
  · exact .structured body C' _ (statementsWellTyped_equiv_congr hbodyTyped heq.1)

/-- **Soundness of `genProcedure` at the ambient context.** Every procedure that `genProcedure`
    makes in a context `C` is well-typed (`ProcWellTyped`) at that same `C` with no enclosing
    variable scope, when every callable procedure resolves in `P`, no type name of `P` is a local
    type name, the operator types and the callee signature types are well kinded in `C`, and the
    operators and schemes agree with `C`. -/
theorem genProcedure_sound_ambient (P : Program) (octx : OpCtx) (procs : ProcSigCtx)
    (hProcs : ProcSigCorresponds procs P)
    (hLocalTypes : ∀ n ∈ programNamesOfKind P .type, ¬ isLocalTypeName n.name)
    (size len : Nat) (C : LContext CoreLParams) (Γ : TContext Unit)
    (hWK : ∀ rv : List TyIdentifier,
      StrataGenerators.Stmt.WellKindedAmbient octx procs { C with rigidTypeVars := rv })
    (pctx : PolyOpCtx) (hops : StrataGenerators.AnnotFacts.ExprCtxOk C [] [] octx pctx)
    (proc : Procedure)
    (hproc : proc ∈ SetGen.support
      (genProcedure (G := SetGen.Set) octx procs C Γ size len pctx)) :
    ProcWellTyped P C [] proc :=
  genProcedure_sound P octx procs hProcs hLocalTypes size len C Γ hWK pctx hops proc hproc

-- ── Completeness ─────────────────────────────────────────────────────────

set_option maxHeartbeats 800000 in
/-- **The completeness of `genProcedure`.** Take a procedure whose signature admits the decomposition of the
    generator into three blocks. The inputs are the shared in-out block and then the input-only block, and the
    outputs are the shared block and then the output-only block. The shared block comes first in both. The keys
    of the input-only block are disjoint from the keys of the shared block, and the keys of the output-only
    block are disjoint from the keys of the other two. If the procedure also has a *structured*
    body, and the sub-generators reach its name, type arguments, three signature blocks, lemma
    names, contract and body, it is in `genProcedure`'s support.

    The three-block disjointness hypotheses (`hIdisjM`, `hOdisjMI`) are the
    completeness-only side-conditions witnessing that the generator's
    `disjointInputs` filters reproduce `I` and `O` unchanged (idempotence, via
    `disjointInputs_eq_self`). The `procs : ProcSigCtx` here is the same call-target
    context `genProcedure` threads into the body; `hBodyReach` is stated against it,
    and `genProcedure_sound`'s only side-condition is the matching
    `ProcSigCorresponds procs P` that certifies those targets against `P`.

    The premises are these:

    - `hInputsEq` and `hOutputsEq` give the decomposition of the signature into three blocks, with the shared
      block first in both the inputs and the outputs.
    - `hName` says that the name of the procedure is a reachable identifier.
    - `hTyArgsLen` and `hTyArgsReach` say that the type arguments, whose names are already distinct, are not more
      than `size` in number, and that `genIdentName` reaches each of them.
    - The premises for each of the three blocks say that its keys are distinct, that its length is inside the
      bound, that `genIdentName` reaches each of its key names, and that `genLMonoTy` reaches each of its values.
    - `hFormalsNotFn` says that no formal parameter is named after a function of `C`, as the
      procedure rule asks.
    - The premises for each contract clause say that its attribute field and its metadata field hold their
      default values, that `genNameList` reaches its list of labels, and that `genLExpr … .bool`
      reaches its expression.
    - `hBodyReach` says that the statement list of the body is in the support of `genStmtChain`, at exactly the
      seed that the generator uses, which is the three blocks and then the old variables, with the keys of the
      inputs and of the old variables as the immutable names, at an empty context of the labels and of the free
      variables,
      type-variable list `typeArgs`, and the ambient `C` with `typeArgs` added to its rigid type
      variables. (A caller can
      obtain this membership from `spec_complete` applied to each body statement.)
    - `hLemmasLen` and `hLemmasReach` say that the lemma names are not more than `size` in number
      and that `genIdentName` reaches each of them.

    The block name-length / reachability conditions are stated concretely via
    `mem_support_genNameList_iff`. -/
theorem genProcedure_complete (octx : OpCtx) (procs : ProcSigCtx)
    (C : LContext CoreLParams) (Γ : TContext Unit) (size len : Nat)
    (proc : Procedure)
    (M I O : ListMap (Identifier Unit) LMonoTy)
    (bodyss : List Statement) (C' : LContext CoreLParams) (ctx' : VarCtx)
    -- the generator makes only a structured body:
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
    -- no formal parameter is named after a function:
    (hFormalsNotFn : ∀ id ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      id.name ∉ C.functions)
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
        { C with rigidTypeVars := C.rigidTypeVars ++ proc.header.typeArgs }
        (M ++ I ++ (M ++ O) ++ oldVars M) [] size len))
    (hLemmasLen : proc.header.lemmas.length ≤ size)
    (hLemmasReach : ∀ s ∈ proc.header.lemmas, s ∈ SetGen.support (genIdentName (G := SetGen.Set))) :
    proc ∈ SetGen.support (genProcedure (G := SetGen.Set) octx procs C Γ size len) := by
  simp only [genProcedure, genProcedureWith, mem_support_bind_iff, mem_support_pure_iff]
  -- The generator's `disjointInputs` filters reproduce `I` and `O` unchanged.
  have hI_eq : disjointInputs I M = I := disjointInputs_eq_self I M hIdisjM
  have hO_eq : disjointInputs O (M ++ I) = O := disjointInputs_eq_self O (M ++ I) hOdisjMI
  -- No block has a key named after a function, so `avoidFunctionNames` keeps each of them.
  have hFormals : ∀ id ∈ ListMap.keys (M ++ I) ++ ListMap.keys (M ++ O), id.name ∉ C.functions := by
    rw [← hInputsEq, ← hOutputsEq]; exact hFormalsNotFn
  have hMeq : avoidFunctionNames C M = M := by
    refine avoidFunctionNames_eq_self C M (fun k hk => hFormals k ?_)
    rw [ListMap_keys_append]
    exact List.mem_append_left _ (List.mem_append_left _ hk)
  have hIeq : avoidFunctionNames C I = I := by
    refine avoidFunctionNames_eq_self C I (fun k hk => hFormals k ?_)
    rw [ListMap_keys_append]
    exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hOeq : avoidFunctionNames C O = O := by
    refine avoidFunctionNames_eq_self C O (fun k hk => hFormals k ?_)
    rw [ListMap_keys_append, ListMap_keys_append]
    exact List.mem_append_right _ (List.mem_append_right _ hk)
  -- Witnesses: name, type args, the three blocks `M`/`I`/`O`, contracts, body triple.
  refine ⟨proc.header.name.name, hName,
          proc.header.typeArgs, ?_,
          M, ?_,
          I, ?_,
          O, ?_,
          proc.spec.preconditions, ?_,
          proc.spec.postconditions, ?_,
          (bodyss, C', ctx'), ?_,
          proc.header.lemmas, mem_support_genNameList_iff size _ |>.mpr ⟨hLemmasLen, hLemmasReach⟩,
          ?_⟩
  · exact genTypeArgs_complete size proc.header.typeArgs hTyArgsNodup
      (mem_support_genNameList_iff size _ |>.mpr ⟨hTyArgsLen, hTyArgsReach⟩)
  · exact genInputs_complete _ size M hMNodup
      (mem_support_genNameList_iff size _ |>.mpr ⟨hMNamesLen, hMNamesReach⟩) hMTyReach
  · exact genInputs_complete _ size I hINodup
      (mem_support_genNameList_iff size _ |>.mpr ⟨hINamesLen, hINamesReach⟩) hITyReach
  · exact genInputs_complete _ size O hONodup
      (mem_support_genNameList_iff size _ |>.mpr ⟨hONamesLen, hONamesReach⟩) hOTyReach
  · rw [hMeq, hIeq, hI_eq]
    exact genChecks_complete (sigFctx (M ++ I))
      octx proc.header.typeArgs size proc.spec.preconditions
      hPreLabels hPreAttr hPreMd hPreExpr
  · rw [hMeq, hIeq, hI_eq, hOeq, hO_eq]
    exact genChecks_complete (sigFctx (M ++ I ++ (M ++ O) ++ oldVars M))
      octx proc.header.typeArgs size proc.spec.postconditions
      hPostLabels hPostAttr hPostMd hPostExpr
  · -- body reachable: the generator's filtered blocks equal `M`/`I`/`O`; `hBodyReach`
    -- is the body's `genStmtChain` support membership directly.
    rw [hMeq, hIeq, hI_eq, hOeq, hO_eq]
    exact hBodyReach
  · -- the reassembled record equals `proc`.
    rw [hMeq, hIeq, hI_eq, hOeq, hO_eq]
    obtain ⟨⟨pname, ptyArgs, pinputs, poutputs, plemmas⟩, ⟨ppre, ppost⟩, pbody⟩ := proc
    obtain ⟨nm, nmeta⟩ := pname
    simp only at hInputsEq hOutputsEq hBodyEq ⊢
    subst hBodyEq hInputsEq hOutputsEq
    rfl

end StrataGenerators.Procedure
