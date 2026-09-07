import Flapjack.RiscV.CorrectnessCondition

namespace Flapjack.RiscV

example [NeZero width] (state : State width) (operator : Cmp)
    (condition source : Nat)
    (branchLeft right : Fin 32) (prelude : List (Instruction width))
    (hzero : ZeroRegister state)
    (hoperands : wordConditionOperands operator condition (.reg source) =
      some (branchLeft, right, prelude)) :
    evalWordCondition state operator condition (.reg source) =
      riscVCondition (executeInstructions state prelude) operator branchLeft right := by
  exact wordConditionOperands_register_sound state operator condition source hzero
    branchLeft right prelude hoperands

example [NeZero width] (state : State width) (operator : Cmp)
    (condition : Nat) (branchLeft right : Fin 32)
    (prelude : List (Instruction width)) (hzero : ZeroRegister state)
    (hoperands : wordConditionOperands operator condition (.imm 0) =
      some (branchLeft, right, prelude)) :
    evalWordCondition state operator condition (.imm 0) =
      riscVCondition (executeInstructions state prelude) operator branchLeft right := by
  exact wordConditionOperands_immediate_zero_sound state operator condition hzero
    branchLeft right prelude hoperands

example [NeZero width] (state : State width) (operator : Cmp)
    (condition : Nat) (value : Word width) (branchLeft right : Fin 32)
    (prelude : List (Instruction width)) (hzero : ZeroRegister state)
    (hoperands : wordConditionOperands operator condition (.imm value) =
      some (branchLeft, right, prelude)) :
    evalWordCondition state operator condition (.imm value) =
      riscVCondition (executeInstructions state prelude) operator branchLeft right := by
  exact wordConditionOperands_immediate_sound state operator condition value hzero
    branchLeft right prelude hoperands

end Flapjack.RiscV
