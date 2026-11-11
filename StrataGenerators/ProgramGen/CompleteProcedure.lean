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

The polymorphic operator context is the program's `s.derivedPctx`, as `genDeclProcedure` passes it.
-/

open Lambda RandomChoice Core Imperative SPMF
open StrataGenerators StrataGenerators.Procedure StrataGenerators.Stmt.SpecComplete

namespace ProgramGen

/-- The state after the procedure step declares `proc` under the name `nm`: the name is reserved, and
    the call signature is recorded, as `genDeclProcedure` computes it. -/
def procStepState (s : GenState) (proc : Procedure) (nm : String) : GenState :=
  let M := commonPrefix proc.header.inputs proc.header.outputs
  { s with reserved := nm :: s.reserved,
           procs := { pname := nm, typeArgs := proc.header.typeArgs, M := M,
                      I := proc.header.inputs.drop M.length,
                      O := proc.header.outputs.drop M.length } :: s.procs }

/-- **The procedure step reaches every procedure that `genProcedure` reaches eventually**, for every
    bounds record with a large enough `procSize` and `maxStmtSeqLen` and a `procLen` at least the
    body's length, under a fresh, allowed name. -/
theorem genDeclProcedure_complete {s : GenState} {proc : Procedure} {nm : String} {L : Nat}
    (hname : proc.header.name = ⟨nm, ()⟩)
    (hnm : nm ∈ SPMF.support (DatatypeGen.genFreshName (G := SPMF) s.reserved))
    (hallowed : isAllowedName nm = true)
    (hproc : ∃ K, Eventually fun size => ∀ len k, L ≤ len → K ≤ k →
      proc ∈ SPMF.support (genProcedure (G := SPMF) s.octx s.procs s.C s.Γ size len s.derivedPctx
        (maxStmtSeqLen := k))) :
    ∃ K N, ∀ b : Bounds, N ≤ b.procSize → L ≤ b.procLen → K ≤ b.maxStmtSeqLen →
      ([.proc proc .empty], procStepState s proc nm) ∈
        SPMF.support (genDeclProcedure (G := SPMF) s b) := by
  obtain ⟨K, N, h⟩ := hproc
  refine ⟨K, N, fun b hN hL hK => ?_⟩
  have hrename : { proc with header := { proc.header with name := ⟨nm, ()⟩ } } = proc := by
    rw [← hname]
  simp only [genDeclProcedure, mem_support_bind_iff, mem_support_pure_iff]
  exact ⟨proc, h b.procSize hN b.procLen b.maxStmtSeqLen hL hK, nm,
    genDeclName_complete hnm hallowed, Prod.ext (by rw [hrename]) rfl⟩

end ProgramGen
