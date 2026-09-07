import Flapjack.RiscV.CorrectnessCode

/-!
Machine-level control-flow correctness for the smallest conditional layout
emitted by the Word backend.  The general lowering uses the same layout:
branch over the then block, execute an unconditional jump over the else block,
then stop at the first byte after the conditional.
-/

namespace Flapjack.RiscV

def advancesPc (instruction : Instruction 64) : Prop :=
  ∀ state : State 64, (execute state instruction).pc = nextPc state

theorem executeCode_conditional_single
    (state : State 64) (operator : Cmp) (left right : Fin 32)
    (thenInstruction elseInstruction : Instruction 64)
    (hpc : state.pc = 0)
    (hthen : advancesPc thenInstruction)
    (helse : advancesPc elseInstruction) :
    executeCode 5 0
        [ riscVBranchFalseInstruction operator left right (BitVec.ofNat 64 12)
        , thenInstruction
        , .branchEq 0 0 (BitVec.ofNat 64 8)
        , elseInstruction ] state =
      if riscVCondition state operator left right then
        some (execute
          (execute
            (execute state
              (riscVBranchFalseInstruction operator left right (BitVec.ofNat 64 12)))
            thenInstruction)
          (.branchEq 0 0 (BitVec.ofNat 64 8)))
      else
        some (execute
          (execute state
            (riscVBranchFalseInstruction operator left right (BitVec.ofNat 64 12)))
          elseInstruction) := by
  let branch := riscVBranchFalseInstruction operator left right (BitVec.ofNat 64 12)
  let jump : Instruction 64 := .branchEq 0 0 (BitVec.ofNat 64 8)
  have hbranch := execute_riscVBranchFalse_pc state operator left right
    (BitVec.ofNat 64 12)
  by_cases hcondition : riscVCondition state operator left right
  · have hbranchPc : (execute state branch).pc = 4 := by
      simpa [branch, hcondition, hpc, nextPc] using hbranch
    have hthenPc : (execute (execute state branch) thenInstruction).pc = 8 := by
      rw [hthen]
      simp [hbranchPc, nextPc]
    have hjumpPc :
        (execute (execute (execute state branch) thenInstruction) jump).pc = 16 := by
      change (execute (execute (execute state branch) thenInstruction)
        (.branchEq 0 0 (BitVec.ofNat 64 8))).pc = 16
      rw [execute_branchEq_pc, hthenPc]
      simp
    have hstep1 :
        executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state =
          executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) := by
      simp [executeCode, hpc]
    have hstep2 :
        executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) =
          executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) thenInstruction) := by
      simp [executeCode, hbranchPc]
    have hstep3 :
        executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) thenInstruction) =
          executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute (execute state branch) thenInstruction) jump) := by
      simp [executeCode, hthenPc]
    have hstep4 :
        executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute (execute state branch) thenInstruction) jump) =
          some (execute (execute (execute state branch) thenInstruction) jump) := by
      simp [executeCode, hjumpPc]
    change executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state = _
    rw [hstep1, hstep2, hstep3, hstep4]
    simp [hcondition, branch, jump]
  · have hbranchPc : (execute state branch).pc = 12 := by
      simpa [branch, hcondition, hpc, nextPc] using hbranch
    have helsePc : (execute (execute state branch) elseInstruction).pc = 16 := by
      rw [helse]
      simp [hbranchPc, nextPc]
    have hstep1 :
        executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state =
          executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) := by
      simp [executeCode, hpc]
    have hstep2 :
        executeCode 4 0 [branch, thenInstruction, jump, elseInstruction]
            (execute state branch) =
          executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) := by
      simp [executeCode, hbranchPc]
    have hstep3 :
        executeCode 3 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) =
          executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) := by
      simp [executeCode, helsePc]
    change executeCode 5 0 [branch, thenInstruction, jump, elseInstruction] state = _
    rw [hstep1, hstep2, hstep3]
    have hend :
        executeCode 2 0 [branch, thenInstruction, jump, elseInstruction]
            (execute (execute state branch) elseInstruction) =
          some (execute (execute state branch) elseInstruction) := by
      simp [executeCode, helsePc]
    rw [hend]
    simp [hcondition, branch]

end Flapjack.RiscV
