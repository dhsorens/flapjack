import Flapjack.RiscV.CorrectnessCondition

/-!
Machine-level control-flow contracts for the branch instructions emitted by
the Word conditional lowering.

The lowering branches to the `else` block when the source condition is false.
This file records that choice independently of code layout; the later
`executeCode` theorem can then use it together with the offset calculation.
-/

namespace Flapjack.RiscV

def riscVBranchFalseInstruction [NeZero width] (operator : Cmp)
    (left right : Fin 32) (offset : Word width) : Instruction width :=
  match operator with
  | .equal => .branchNe left right offset
  | .notEqual => .branchEq left right offset
  | .less => .branchGe left right offset
  | .notLess => .branchLt left right offset
  | .lower => .branchGeU left right offset
  | .notLower => .branchLtU left right offset
  | .test => .branchNe left right offset
  | .notTest => .branchEq left right offset

theorem execute_riscVBranchFalse_pc [NeZero width] (state : State width)
    (operator : Cmp) (left right : Fin 32) (offset : Word width) :
    (execute state (riscVBranchFalseInstruction operator left right offset)).pc =
      if riscVCondition state operator left right then
        nextPc state
      else
        state.pc + offset := by
  cases operator <;>
    simp [riscVBranchFalseInstruction, riscVCondition, execute, nextPc]
  · rfl
  · by_cases h : readRegister state left < readRegister state right
    · have h' : ¬ readRegister state right ≤ readRegister state left :=
        (BitVec.not_le).mpr h
      simp [h, h']
    · have h' : readRegister state right ≤ readRegister state left :=
        (BitVec.not_lt).mp h
      simp [h]
  · by_cases h : signedLess (readRegister state left) (readRegister state right) = true
    · simp [h]
    · have h' : signedLess (readRegister state left) (readRegister state right) = false :=
        eq_false_of_ne_true h
      simp [h]

theorem execute_riscVBranchFalse_pc_of_condition [NeZero width]
    (state : State width) (operator : Cmp) (condition source : Nat)
    (branchLeft right : Fin 32) (prelude : List (Instruction width))
    (offset : Word width) (hzero : ZeroRegister state)
    (hoperands : wordConditionOperands operator condition (.reg source) =
      some (branchLeft, right, prelude)) :
    (execute (executeInstructions state prelude)
      (riscVBranchFalseInstruction operator branchLeft right offset)).pc =
        if evalWordCondition state operator condition (.reg source) = some true then
          nextPc (executeInstructions state prelude)
        else
          (executeInstructions state prelude).pc + offset := by
  rw [execute_riscVBranchFalse_pc]
  have hcondition := wordConditionOperands_register_sound state operator condition source hzero
    branchLeft right prelude hoperands
  rw [hcondition]
  simp

end Flapjack.RiscV
