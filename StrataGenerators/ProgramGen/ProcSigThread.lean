import StrataGenerators.ProgramGen
import StrataGenerators.StmtHasTypeAGen

/-!
# Threading callable procedure signatures through the declaration fold

`genProcedure` accepts a `procs : ProcSigCtx` and will emit `call` statements to
its entries, and `genProcedure_sound` is proved *given*
`ProcSigCorresponds procs P`. The whole-program generator originally passed `[]`,
making that hypothesis vacuous — at the cost that no generated program contained
an inter-procedure call.

This module supplies what is needed to pass a *non-empty* `procs`.

## The difficulty

`ProcSigCorresponds procs P` says each entry resolves in `P` via
`Program.Procedure.find?`. But the fold builds `P` incrementally: when a
procedure declaration is generated, the enclosing program does not exist yet, and
the existing `genDeclsFold_sound` is stated for an *arbitrary* `P` precisely
because no step needed to know it.

So the fold cannot establish `ProcSigCorresponds` step-by-step against a `P` it
has not finished building. What it *can* do is record the signatures it has
emitted so far and prove they resolve in the final program, using two facts:

* `find?` is a **first-match linear scan** (`Program.find?.go`), so a hit in a
  prefix survives appending more declarations — `findGo_append`;
* the fold already proves `P.getNames.Nodup` (`genProgram_getNames_nodup`), so a
  later declaration cannot shadow an earlier procedure's name.

Together: a procedure emitted at step `i` is found by `find?` in the *whole*
program, which is exactly `ProcSigCorresponds` for the accumulated context.
-/

open Lambda RandomChoice Core Core.TypeSpec Imperative SetGen
open DatatypeGen
open StrataGenerators.Procedure StrataGenerators.Stmt

namespace ProgramGen

/-! ## `find?` under append -/

/-- **The scan distributes over append.** `Program.find?.go` walks the list in
    order and stops at the first match, so searching `pre ++ suf` is: search
    `pre`, and fall through to `suf` only on a miss. -/
theorem findGo_append (k : DeclKind) (x : Expression.Ident) (pre suf : List Decl) :
    Program.find?.go k x (pre ++ suf) =
      match Program.find?.go k x pre with
      | some d => some d
      | none => Program.find?.go k x suf := by
  induction pre with
  | nil => simp [Program.find?.go]
  | cons d rest ih =>
    simp only [List.cons_append, Program.find?.go]
    split <;> simp [ih]

/-- A declaration list containing `d` at a position no earlier occurrence
    shadows is found by the scan. The "no earlier occurrence" side condition is
    stated as: `d.name` does not occur among the names of the strict prefix. -/
theorem findGo_of_mem_of_prefix_fresh {k : DeclKind} {x : Expression.Ident}
    {pre : List Decl} {d : Decl} (suf : List Decl)
    (hk : d.kind = k) (hx : d.name = x)
    (hfresh : ∀ d' ∈ pre, ¬ (d'.kind = k ∧ d'.name = x)) :
    Program.find?.go k x (pre ++ d :: suf) = some d := by
  induction pre with
  | nil =>
    simp only [List.nil_append, Program.find?.go]
    rw [if_pos (by simp [hk, hx])]
  | cons d' rest ih =>
    simp only [List.cons_append, Program.find?.go]
    rw [if_neg (by
      intro hmatch
      simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
      exact hfresh d' List.mem_cons_self hmatch)]
    exact ih (fun d'' hd'' => hfresh d'' (List.mem_cons_of_mem _ hd''))

/-! ## From an emitted procedure declaration to `Procedure.find?`

A `.proc p .empty` declaration has `kind = .proc` and `name = p.header.name`, so
the two lemmas above locate it. `Program.Procedure.find?` then unwraps it. -/

/-- `Decl.kind` of an emitted procedure declaration. -/
@[simp] theorem decl_proc_kind (p : Procedure) (md : MetaData Expression) :
    (Decl.proc p md).kind = .proc := rfl

/-- `Decl.name` of an emitted procedure declaration. -/
@[simp] theorem decl_proc_name (p : Procedure) (md : MetaData Expression) :
    (Decl.proc p md).name = p.header.name := rfl

/-- **A procedure emitted in the declaration list resolves via
    `Program.Procedure.find?`.** Given the whole list split around the procedure's
    own declaration, and that no earlier declaration is a procedure of the same
    name, `find?` returns exactly that procedure. -/
theorem procedure_find?_of_split {pre suf : List Decl} {p : Procedure}
    {md : MetaData Expression}
    (hfresh : ∀ d' ∈ pre, ¬ (d'.kind = .proc ∧ d'.name = p.header.name)) :
    Program.Procedure.find? { decls := pre ++ Decl.proc p md :: suf } p.header.name
      = some p := by
  have hgo : Program.find? { decls := pre ++ Decl.proc p md :: suf } .proc p.header.name
      = some (Decl.proc p md) := by
    show Program.find?.go .proc p.header.name (pre ++ Decl.proc p md :: suf) = _
    exact findGo_of_mem_of_prefix_fresh suf rfl rfl hfresh
  -- `Procedure.find?` matches on `find?` and unwraps with `Decl.getProc`, which
  -- reduces on the `.proc` constructor.
  rw [Program.Procedure.find?]
  -- The `match` is dependent (it binds the equation `H`), so case on it and use
  -- `hgo` to kill the `none` branch and identify the `some` branch's payload.
  split
  · rename_i hnone; rw [hgo] at hnone; exact absurd hnone (by simp)
  · rename_i d hsome
    rw [hgo] at hsome
    injection hsome with hd
    subst hd
    rfl

/-! ## The signature a generated procedure contributes

`genProcedure` builds `inputs = M ++ I` and `outputs = M ++ O` from three
mutually disjoint blocks (`ProcedureHasTypeAGen/Core.lean`), which is exactly the
decomposition `ProcSig` records. `genProcedure_sig` reads those blocks back off
the support so the fold can register the callee. -/

/-- The `ProcSig` describing a procedure, given its `M`/`I`/`O` decomposition. -/
def procSigOf (p : Procedure) (M I O : @LMonoTySignature Unit) :
    ProcSig :=
  { pname := p.header.name.name
    typeArgs := p.header.typeArgs
    M := M, I := I, O := O }

/-- **A generated procedure exposes an `M`/`I`/`O` decomposition.** Reading the
    blocks back off `genProcedure`'s support: `inputs = M ++ I`,
    `outputs = M ++ O`, and `I`'s keys avoid `(M ++ O)`'s keys — the three clauses
    `ProcSigCorresponds` asks for, besides `find?` resolution.

    The disjointness clause comes from `disjointInputs`: the generator builds
    `I := disjointInputs rawInputOnly M` and
    `O := disjointInputs rawOutputOnly (M ++ I)`, and
    `disjointInputs_key_not_output` says a surviving `I` key is not an `M` key.
    Avoiding the `O` keys is the symmetric fact, since `O` was itself filtered
    against `M ++ I`. -/
theorem genProcedure_sig_decomp {octx : OpCtx} {procs : ProcSigCtx}
    {C : LContext CoreLParams} {Γ : TContext Unit} {size len : Nat} {p : Procedure}
    (hp : p ∈ SetGen.support (genProcedure (G := SetGen.Set) octx procs C Γ size len)) :
    ∃ M I O : @LMonoTySignature Unit,
      p.header.inputs = M ++ I ∧ p.header.outputs = M ++ O ∧
      (∀ i (hi : i < I.keys.length), (M ++ O).keys.contains (I.keys[i]'hi) = false) := by
  simp only [genProcedure, mem_support_bind_iff, mem_support_pure_iff] at hp
  obtain ⟨name, _hname, typeArgs, _htypeArgs, M, _hM, rawInputOnly, _hrawIn,
          rawOutputOnly, _hrawOut, pre, _hpre, post, _hpost,
          ⟨body, C', ctx'⟩, _hbody, rfl⟩ := hp
  refine ⟨M, disjointInputs rawInputOnly M,
          disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M), rfl, rfl, ?_⟩
  intro i hi
  -- The `i`-th `I` key is a key of `I`, hence not an `M` key; and `O` was filtered
  -- against `M ++ I`, so it is not an `O` key either.
  have hmem : (disjointInputs rawInputOnly M).keys[i]'hi
      ∈ ListMap.keys (disjointInputs rawInputOnly M) :=
    List.getElem_mem hi
  have hnotM : (disjointInputs rawInputOnly M).keys[i]'hi ∉ ListMap.keys M :=
    disjointInputs_key_not_output rawInputOnly M _ hmem
  have hnotO : (disjointInputs rawInputOnly M).keys[i]'hi ∉
      ListMap.keys (disjointInputs rawOutputOnly (M ++ disjointInputs rawInputOnly M)) := by
    intro hO
    -- An `O` key avoids every `M ++ I` key, but this one *is* an `I` key.
    exact disjointInputs_key_not_output rawOutputOnly (M ++ disjointInputs rawInputOnly M) _ hO
      (by rw [ListMap_keys_append]; exact List.mem_append_right _ hmem)
  rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem, ListMap_keys_append]
  intro hcontra
  rcases List.mem_append.mp hcontra with h | h
  · exact hnotM h
  · exact hnotO h



/-! ## Antitonicity, and the shape of the top-level obligation

`ProcSigCorresponds procs P` is a `∀` over `procs`, hence **antitone**: it holds
for any sublist. The fold only ever *grows* `procs` (each procedure step prepends).
So rather than re-establish the property at every step against a program that does
not exist yet, we:

1. state per-step soundness under `ProcSigCorresponds s.procs P` as a hypothesis;
2. observe that the *final* state's `procs` is a superlist of every intermediate
   one, so a single `ProcSigCorresponds sf.procs P` implies all of them;
3. discharge that one obligation at the top level, where `P` *is* the finished
   program.

`ProcsEmitted` is the bookkeeping for step 3: it records that every registered
signature really describes a `.proc` declaration present in the emitted list. -/

/-- `ProcSigCorresponds` is antitone in the signature list. -/
theorem ProcSigCorresponds.mono {procs procs' : ProcSigCtx} {P : Program}
    (h : ProcSigCorresponds procs' P) (hsub : ∀ s ∈ procs, s ∈ procs') :
    ProcSigCorresponds procs P :=
  fun s hs => h s (hsub s hs)

/-- Every registered signature describes a procedure declaration that is present
    in `decls`, with the `M`/`I`/`O` decomposition it records. -/
def ProcsEmitted (procs : ProcSigCtx) (decls : List Decl) : Prop :=
  ∀ sig ∈ procs, ∃ (p : Procedure) (md : MetaData Expression),
    Decl.proc p md ∈ decls ∧
    p.header.name = ⟨sig.pname, ()⟩ ∧
    p.header.typeArgs = sig.typeArgs ∧
    p.header.inputs = sig.M ++ sig.I ∧
    p.header.outputs = sig.M ++ sig.O ∧
    (∀ i (hi : i < sig.I.keys.length), (sig.M ++ sig.O).keys.contains (sig.I.keys[i]'hi) = false)

/-! ## Membership + `Nodup` ⇒ `find?` resolution

`procedure_find?_of_split` needs the list split around the declaration *and* that
no earlier declaration shares the kind and name. `Program.getNames.Nodup` supplies
the latter: a repeated procedure name would repeat in `getNames`. -/

/-- `Decl.names` of a procedure declaration is the singleton of its name. -/
theorem decl_proc_names (p : Procedure) (md : MetaData Expression) :
    (Decl.proc p md).names = [p.header.name] := rfl

/-- **A procedure declaration present in a name-distinct program resolves.**
    Splitting `decls` at the declaration, `Nodup` of `getNames` rules out an
    earlier declaration carrying the same name, which is what the scan needs. -/
theorem procedure_find?_of_mem {decls : List Decl} {p : Procedure}
    {md : MetaData Expression}
    (hmem : Decl.proc p md ∈ decls)
    (hnodup : (Program.mk (decls := decls)).getNames.Nodup) :
    Program.Procedure.find? { decls := decls } p.header.name = some p := by
  obtain ⟨pre, suf, rfl⟩ := List.append_of_mem hmem
  refine procedure_find?_of_split (md := md) ?_
  intro d' hd' ⟨_hkind, hname⟩
  -- `d'.name ∈ d'.names`, and `p.header.name ∈ (Decl.proc p md).names`, so the
  -- shared name occurs twice in `getNames` — contradicting `Nodup`.
  have hgn : (Program.mk (decls := pre ++ Decl.proc p md :: suf)).getNames
      = (pre.flatMap Decl.names) ++ (Decl.proc p md).names ++ (suf.flatMap Decl.names) := by
    simp only [Program.getNames, Program.getNames.go, List.flatMap_append,
      List.flatMap_cons, List.append_assoc]
  rw [hgn] at hnodup
  have hd'name : d'.name ∈ pre.flatMap Decl.names := by
    refine List.mem_flatMap.mpr ⟨d', hd', ?_⟩
    -- Every declaration's own name is among its `names`.
    cases d' with
    | type t m => exact absurd _hkind (by simp [Decl.kind])
    | ax a m => exact absurd _hkind (by simp [Decl.kind])
    | distinct n es m => exact absurd _hkind (by simp [Decl.kind])
    | proc p' m => simp [Decl.names, Decl.name]
    | func f m => exact absurd _hkind (by simp [Decl.kind])
    | recFuncBlock fs m => exact absurd _hkind (by simp [Decl.kind])
  rw [hname] at hd'name
  -- `++` is left-associative, so the outer split is
  -- `(pre_names ++ proc_names) ++ suf_names`; take the *inner* one.
  have hinner : (List.flatMap Decl.names pre ++ (Decl.proc p md).names).Nodup :=
    (List.nodup_append.mp hnodup).1
  have hnd := (List.nodup_append.mp hinner).2.2
  exact hnd _ hd'name _ (by rw [decl_proc_names]; exact List.mem_singleton_self _) rfl

/-- **The top-level obligation, discharged.** If every registered signature
    describes a procedure declaration present in the program, and the program's
    names are distinct, then `ProcSigCorresponds` holds for the whole accumulated
    context. -/
theorem procSigCorresponds_of_emitted {procs : ProcSigCtx} {decls : List Decl}
    (hem : ProcsEmitted procs decls)
    (hnodup : (Program.mk (decls := decls)).getNames.Nodup) :
    ProcSigCorresponds procs { decls := decls } := by
  intro sig hsig
  obtain ⟨p, md, hmem, hname, htyArgs, hins, houts, hdisj⟩ := hem sig hsig
  refine ⟨p, ?_, htyArgs, hins, houts, hdisj⟩
  rw [← hname]
  exact procedure_find?_of_mem hmem hnodup



/-! ## `procs` grows monotonically across the fold

Only `genDeclProcedure` touches `procs`, and it *prepends*. Every other step
copies it. So the accumulated context only grows, which — with
`ProcSigCorresponds.mono` — lets the fold consume a single correspondence for the
*final* state at every intermediate step. -/

/-- One declaration step never drops a registered signature. -/
theorem genDeclStep_procs_mono {s s' : GenState} {b : Bounds} {ds : List Decl}
    (h : (ds, s') ∈ SetGen.support (genDeclStep (G := SetGen.Set) s b)) :
    ∀ sig ∈ s.procs, sig ∈ s'.procs := by
  -- `genDeclStep` is a weighted `frequency`; support inversion yields a
  -- `(weight, generator)` pair, so the branch equations pin both components.
  simp only [genDeclStep, mem_support_frequency_iff, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at h
  obtain ⟨w, g, hg, _hw, hmem⟩ := h
  rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  -- Abstract: gated; both branches copy `procs`.
  · simp only [genDeclAbstract, genAbstractType, mem_support_bind_iff,
      mem_support_pure_iff] at hmem
    obtain ⟨pr, ⟨nm, _, ar, _, hpr⟩, hmatch⟩ := hmem
    subst hpr
    simp only at hmatch
    split at hmatch
    all_goals (
      simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
      obtain ⟨_, hs'⟩ := hmatch; subst hs'; exact fun _ h => h)
  -- Alias / axiom / distinct: `procs` copied.
  · simp only [genDeclAlias, genAlias, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨pr, _, _, hs'⟩ := hmem; subst hs'; exact fun _ h => h
  · simp only [genDeclAxiom, genAxiom, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨pr, _, _, hs'⟩ := hmem; subst hs'; exact fun _ h => h
  -- Distinct: gated on the constants' factory adds; both branches copy `procs`.
  · simp only [genDeclDistinct, mem_support_bind_iff] at hmem
    obtain ⟨pr, _, hmatch⟩ := hmem
    split at hmatch
    all_goals (
      simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
      obtain ⟨_, hs'⟩ := hmatch; subst hs'; exact fun _ h => h)
  -- Datatype: gated; both branches copy `procs`.
  · simp only [genDeclDatatype, mem_support_bind_iff] at hmem
    obtain ⟨block, _, hmatch⟩ := hmem
    split at hmatch
    all_goals (
      simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
      obtain ⟨_, hs'⟩ := hmatch; subst hs'; exact fun _ h => h)
  -- Function: gated; both branches copy `procs`. `split` cases the `match` without
  -- naming the (projection-typed) scrutinee.
  · simp only [genDeclFunction, mem_support_bind_iff] at hmem
    obtain ⟨func₀, _, nm, _, hmatch⟩ := hmem
    split at hmatch
    all_goals (
      simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
      obtain ⟨_, hs'⟩ := hmatch; subst hs'; exact fun _ h => h)
  -- Procedure: `procs` gains one entry at the front.
  · simp only [genDeclProcedure, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨proc₀, _, nm, _, _, hs'⟩ := hmem
    subst hs'
    exact fun sig hsig => List.mem_cons_of_mem _ hsig

/-- The whole fold never drops a registered signature. -/
theorem genDeclsFold_procs_mono {s s' : GenState} {b : Bounds} {ds : List Decl}
    (n : Nat) (h : (ds, s') ∈ SetGen.support (genDeclsFold (G := SetGen.Set) s b n)) :
    ∀ sig ∈ s.procs, sig ∈ s'.procs := by
  induction n generalizing s ds s' with
  | zero =>
    simp only [genDeclsFold, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨_, hs'⟩ := h; subst hs'; exact fun _ h => h
  | succ n ih =>
    simp only [genDeclsFold, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨⟨ds₁, s₁⟩, hstep, ⟨rest, s₂⟩, hrest, _, hs'⟩ := h
    subst hs'
    exact fun sig hsig => ih hrest sig (genDeclStep_procs_mono hstep sig hsig)




/-! ## `ProgramGen.commonPrefix` recovers the shared block `M`

The generator registers a callee by recomputing `M` as the longest common prefix
of `inputs`/`outputs`. That is exact for a generated procedure:
`lcp (M ++ I) (M ++ O) = M ++ lcp I O`, and `lcp I O = []` because `I` and `O`
have disjoint keys — so their first entries differ whenever both are non-empty. -/

/-- `ProgramGen.commonPrefix` distributes over a shared prefix. -/
theorem commonPrefixList_append {α : Type} [DecidableEq α] :
    ∀ (M A B : List α),
      ProgramGen.commonPrefixList (M ++ A) (M ++ B)
        = M ++ ProgramGen.commonPrefixList A B := by
  intro M
  induction M with
  | nil => intro A B; rfl
  | cons a as ih =>
    intro A B
    show ProgramGen.commonPrefixList (a :: (as ++ A)) (a :: (as ++ B))
        = a :: (as ++ ProgramGen.commonPrefixList A B)
    rw [ProgramGen.commonPrefixList, if_pos rfl, ih A B]

/-- Two signatures whose *keys* are disjoint have no common prefix: a shared
    leading entry would share its key. -/
theorem commonPrefix_eq_nil_of_disjoint {A B : List (Identifier Unit × LMonoTy)}
    (h : ∀ k ∈ ListMap.keys A, k ∉ ListMap.keys B) :
    ProgramGen.commonPrefixList A B = [] := by
  cases A with
  | nil => rfl
  | cons a as =>
    cases B with
    | nil => rfl
    | cons b bs =>
      simp only [ProgramGen.commonPrefixList]
      rw [if_neg]
      intro heq
      -- `a = b` would put `a.1` in both key lists.
      refine h a.1 ?_ ?_
      · rw [ListMap.keys_eq_map_fst]; exact List.mem_map.mpr ⟨a, List.mem_cons_self, rfl⟩
      · rw [ListMap.keys_eq_map_fst]
        exact List.mem_map.mpr ⟨b, List.mem_cons_self, by rw [heq]⟩

/-- **`ProgramGen.commonPrefix` is exact on a decomposed signature pair.** -/
theorem commonPrefix_of_decomp {M I O : List (Identifier Unit × LMonoTy)}
    (h : ∀ k ∈ ListMap.keys I, k ∉ ListMap.keys O) :
    ProgramGen.commonPrefixList (M ++ I) (M ++ O) = M := by
  rw [commonPrefixList_append, commonPrefix_eq_nil_of_disjoint h]
  exact List.append_nil M


/-! ## Recovering the decomposition from a generated procedure

`genDeclProcedure` registers a callee using `commonPrefix` on the procedure's
`inputs`/`outputs`. `genProcedure_sig_decomp` says the support *has* a
decomposition `inputs = M ++ I`, `outputs = M ++ O` with `I`/`O` key-disjoint;
`commonPrefix_of_decomp` says `commonPrefix` finds exactly that `M`. Combining
them gives the registered signature's three clauses. -/

/-- `I`'s keys avoid `O`'s keys, extracted from the `(M ++ O)`-avoidance clause. -/
theorem keys_disjoint_of_decomp {M I O : @LMonoTySignature Unit}
    (hdisj : ∀ i (hi : i < I.keys.length), (M ++ O).keys.contains (I.keys[i]'hi) = false) :
    ∀ k ∈ ListMap.keys I, k ∉ ListMap.keys O := by
  intro k hk hO
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hk
  have hcon := hdisj j hj
  rw [hje, Bool.eq_false_iff, ne_eq, List.contains_iff_mem, ListMap_keys_append] at hcon
  exact hcon (List.mem_append_right _ hO)

/-- **The registered signature is correct.** For a procedure in `genProcedure`'s
    support, `commonPrefix inputs outputs` is the shared block `M`, and dropping
    its length off each signature yields `I` and `O`. -/
theorem genProcedure_commonPrefix_decomp {octx : OpCtx} {procs : ProcSigCtx}
    {C : LContext CoreLParams} {Γ : TContext Unit} {size len : Nat} {p : Procedure}
    (hp : p ∈ SetGen.support (genProcedure (G := SetGen.Set) octx procs C Γ size len)) :
    ∃ M I O : @LMonoTySignature Unit,
      ProgramGen.commonPrefix p.header.inputs p.header.outputs = M ∧
      p.header.inputs.drop M.length = I ∧
      p.header.outputs.drop M.length = O ∧
      p.header.inputs = M ++ I ∧ p.header.outputs = M ++ O ∧
      (∀ i (hi : i < I.keys.length), (M ++ O).keys.contains (I.keys[i]'hi) = false) := by
  obtain ⟨M, I, O, hins, houts, hdisj⟩ := genProcedure_sig_decomp hp
  refine ⟨M, I, O, ?_, ?_, ?_, hins, houts, hdisj⟩
  · show ProgramGen.commonPrefixList p.header.inputs p.header.outputs = M
    rw [hins, houts]
    exact commonPrefix_of_decomp (keys_disjoint_of_decomp hdisj)
  · rw [hins]; exact List.drop_left
  · rw [houts]; exact List.drop_left


/-! ## `ProcsEmitted` across the fold -/

/-- One step's effect on `procs`: unchanged, or one entry prepended describing the
    procedure the step emitted. -/
theorem genDeclStep_procs_step {s s' : GenState} {b : Bounds} {ds : List Decl}
    (h : (ds, s') ∈ SetGen.support (genDeclStep (G := SetGen.Set) s b)) :
    s'.procs = s.procs ∨
      ∃ (p : Procedure) (sig : ProcSig),
        ds = [Decl.proc p .empty] ∧ s'.procs = sig :: s.procs ∧
        p.header.name = ⟨sig.pname, ()⟩ ∧
        p.header.typeArgs = sig.typeArgs ∧
        p.header.inputs = sig.M ++ sig.I ∧
        p.header.outputs = sig.M ++ sig.O ∧
        (∀ i (hi : i < sig.I.keys.length),
          (sig.M ++ sig.O).keys.contains (sig.I.keys[i]'hi) = false) := by
  -- `genDeclStep` is a weighted `frequency`; support inversion yields a
  -- `(weight, generator)` pair, so the branch equations pin both components.
  simp only [genDeclStep, mem_support_frequency_iff, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at h
  obtain ⟨w, g, hg, _hw, hmem⟩ := h
  rcases hg with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · left
    simp only [genDeclAbstract, genAbstractType, mem_support_bind_iff,
      mem_support_pure_iff] at hmem
    obtain ⟨pr, ⟨nm, _, ar, _, hpr⟩, hmatch⟩ := hmem
    subst hpr; simp only at hmatch
    split at hmatch
    all_goals (simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
               obtain ⟨_, hs'⟩ := hmatch; subst hs'; rfl)
  · left
    simp only [genDeclAlias, genAlias, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨pr, _, _, hs'⟩ := hmem; subst hs'; rfl
  · left
    simp only [genDeclAxiom, genAxiom, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨pr, _, _, hs'⟩ := hmem; subst hs'; rfl
  · left
    simp only [genDeclDistinct, mem_support_bind_iff] at hmem
    obtain ⟨pr, _, hmatch⟩ := hmem
    split at hmatch
    all_goals (simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
               obtain ⟨_, hs'⟩ := hmatch; subst hs'; rfl)
  · left
    simp only [genDeclDatatype, mem_support_bind_iff] at hmem
    obtain ⟨block, _, hmatch⟩ := hmem
    split at hmatch
    all_goals (simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
               obtain ⟨_, hs'⟩ := hmatch; subst hs'; rfl)
  · left
    simp only [genDeclFunction, mem_support_bind_iff] at hmem
    obtain ⟨func₀, _, nm, _, hmatch⟩ := hmem
    split at hmatch
    all_goals (simp only [mem_support_pure_iff, Prod.mk.injEq] at hmatch
               obtain ⟨_, hs'⟩ := hmatch; subst hs'; rfl)
  · right
    simp only [genDeclProcedure, mem_support_bind_iff, mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨proc₀, hproc₀, nm, _hnm, hds, hs'⟩ := hmem
    -- Renaming leaves `inputs`/`outputs`/`typeArgs` alone, so the decomposition
    -- recovered from `proc₀`'s support is the renamed procedure's decomposition too.
    obtain ⟨M, I, O, hcp, hdI, hdO, hins, houts, hdisj⟩ :=
      genProcedure_commonPrefix_decomp hproc₀
    subst hs'
    refine ⟨{ proc₀ with header := { proc₀.header with name := ⟨nm, ()⟩ } }, _,
      hds, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show proc₀.header.inputs = _ ++ _
      rw [hcp, hdI]; exact hins
    · show proc₀.header.outputs = _ ++ _
      rw [hcp, hdO]; exact houts
    · show ∀ i (hi : i < _), _ = false
      rw [hcp, hdI, hdO]; exact hdisj

/-- The whole fold preserves `ProcsEmitted`, relative to the declarations emitted
    so far. Membership survives the append a later step performs. -/
theorem genDeclsFold_procsEmitted {s s' : GenState} {b : Bounds} {ds : List Decl}
    (n : Nat) (h : (ds, s') ∈ SetGen.support (genDeclsFold (G := SetGen.Set) s b n))
    {prior : List Decl} (hprior : ProcsEmitted s.procs prior) :
    ProcsEmitted s'.procs (prior ++ ds) := by
  induction n generalizing s ds s' prior with
  | zero =>
    simp only [genDeclsFold, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨hds, hs'⟩ := h; subst hds hs'
    simpa using hprior
  | succ n ih =>
    simp only [genDeclsFold, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨⟨ds₁, s₁⟩, hstep, ⟨rest, s₂⟩, hrest, hds, hs'⟩ := h
    subst hds hs'
    -- After the first step, `ProcsEmitted s₁.procs (prior ++ ds₁)`.
    have hstep' : ProcsEmitted s₁.procs (prior ++ ds₁) := by
      rcases genDeclStep_procs_step hstep with heq | ⟨p, sig, hds₁, hprocs, rest'⟩
      · intro sg hsg
        obtain ⟨q, md, hq, r⟩ := hprior sg (heq ▸ hsg)
        exact ⟨q, md, List.mem_append_left _ hq, r⟩
      · intro sg hsg
        rw [hprocs] at hsg
        rcases List.mem_cons.mp hsg with rfl | hsg
        · exact ⟨p, .empty, by rw [hds₁]; exact List.mem_append_right _ (by simp), rest'⟩
        · obtain ⟨q, md, hq, r⟩ := hprior sg hsg
          exact ⟨q, md, List.mem_append_left _ hq, r⟩
    -- Then the tail, re-associating the appends.
    have := ih hrest hstep'
    rw [List.append_assoc] at this
    exact this

end ProgramGen
