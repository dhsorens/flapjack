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

end Flapjack.Test.CorrectnessConditional
