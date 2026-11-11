import StrataGenerators.ProgramGen.Complete
import StrataGenerators.ProcedureHasTypeAGenCompleteExists

/-!
# Per-step reachability: procedures

The procedure step of `genDeclStep` draws a procedure from `genProcedure` at the bounds
`b.procSize`, `b.procLen` and `b.maxStmtSeqLen`, renames it with a fresh declaration name, and
records its call signature. `genDeclProcedure_complete` reaches every procedure that
`genProcedure` reaches at every large enough size, body-length bound and cap, which is the
conclusion of `genProcedure_complete_ev`. So the step inherits the size-free statement
completeness through the procedure's body.

**Limitation.** `genDeclProcedure` passes the program's polymorphic operator context
`s.derivedPctx` to `genProcedure`, and `genProcedure_complete` (with the statement completeness
under it) is stated at the empty one. The lemma therefore asks `s.derivedPctx = []`, which holds
until the program declares a polymorphic datatype.
-/

open Lambda RandomChoice Core Imperative SPMF
open StrataGenerators StrataGenerators.Procedure StrataGenerators.Stmt.SpecComplete

namespace ProgramGen

/-- **The procedure step reaches every procedure that `genProcedure` reaches eventually**, for every
    bounds record with a large enough `procSize` and `maxStmtSeqLen` and a `procLen` at least the
    body's length, under a fresh, allowed name. -/
theorem genDeclProcedure_complete {s : GenState} {proc : Procedure} {nm : String} {L : Nat}
    (hname : proc.header.name = ⟨nm, ()⟩)
    (hnm : nm ∈ SPMF.support (DatatypeGen.genFreshName (G := SPMF) s.reserved))
    (hallowed : isAllowedName nm = true)
    (hpctx : s.derivedPctx = [])
    (hproc : ∃ K, Eventually fun size => ∀ len k, L ≤ len → K ≤ k →
      proc ∈ SPMF.support (genProcedure (G := SPMF) s.octx s.procs s.C s.Γ size len
        (maxStmtSeqLen := k))) :
    ∃ K N, ∀ b : Bounds, N ≤ b.procSize → L ≤ b.procLen → K ≤ b.maxStmtSeqLen →
      ∃ s', ([.proc proc .empty], s') ∈ SPMF.support (genDeclProcedure (G := SPMF) s b) := by
  obtain ⟨K, N, h⟩ := hproc
  refine ⟨K, N, fun b hN hL hK => ?_⟩
  have hrename : { proc with header := { proc.header with name := ⟨nm, ()⟩ } } = proc := by
    rw [← hname]
  simp only [genDeclProcedure, hpctx, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨_, proc, h b.procSize hN b.procLen b.maxStmtSeqLen hL hK, nm,
    genDeclName_complete hnm hallowed, Prod.ext (by rw [hrename]) rfl⟩

end ProgramGen
