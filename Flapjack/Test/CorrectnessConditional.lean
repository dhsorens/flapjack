import Flapjack.RiscV.CorrectnessConditional

namespace Flapjack.Test.CorrectnessConditional

open Flapjack Flapjack.RiscV

example (state : State 64) (operator : Cmp) (left right : Fin 32)
    (thenInstruction elseInstruction : Instruction 64)
    (hpc : state.pc = 0)
    (hthen : advancesPc thenInstruction)
    (helse : advancesPc elseInstruction) :
    executeCode 5 0
        [ riscVBranchFalseInstruction operator left right (BitVec.ofNat 64 12)
        , thenInstruction
        , .branchEq 0 0 (BitVec.ofNat 64 8)
        , elseInstruction ] state |>.isSome := by
  rw [executeCode_conditional_single state operator left right thenInstruction
    elseInstruction hpc hthen helse]
  split <;> simp

example :
    wordFunctionToRiscV
        ((.ite .equal 1 (.reg 2)
          (.assign 3 (.const (1 : Word 64)))
          (.assign 3 (.const (2 : Word 64)))) : WordProg (Word 64)) =
      some ([.branchNe 1 2 (BitVec.ofNat 64 12), .addi 3 0 1,
        .branchEq 0 0 (BitVec.ofNat 64 8), .addi 3 0 2], []) := by
  exact wordFunctionToRiscV_ite_assign

example (state : State 64) (hpc : state.pc = 0)
    (hzero : ZeroRegister state) :
    (executeCode 5 0
      [.branchNe 1 2 (BitVec.ofNat 64 12), .addi 3 0 1,
        .branchEq 0 0 (BitVec.ofNat 64 8), .addi 3 0 2] state).map
      (fun state => readRegister state 3) =
      if readRegister state 1 == readRegister state 2 then
        some (1 : Word 64)
      else
        some (2 : Word 64) := by
  exact executeCode_ite_assign state hpc hzero

end Flapjack.Test.CorrectnessConditional
