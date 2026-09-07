import Flapjack.RiscV.CorrectnessLongMulSpill

/-! Regression coverage for the fully spilled LongMul lowering. -/

namespace Flapjack.RiscV

def longMulSpillConfig : WordStackConfig :=
  { locations := [(0, .stack 2), (1, .stack 3),
      (2, .stack 4), (3, .stack 5), (4, .register 6)]
    scratch := 31
    stackBase := 10
    addressScratch := 29
    specialScratch := 28 }

def longMulSpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset =>
      if offset = 14 then BitVec.ofNat 8 3
      else if offset = 15 then BitVec.ofNat 8 4 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

example :
    wordStackMachineValue longMulSpillConfig
      (((wordStackLongMulInst longMulSpillConfig
        (.longMul 0 1 2 3)).bind
        (evalWordStackMachine longMulSpillState)).getD longMulSpillState) 4 =
      wordStackMachineValue longMulSpillConfig longMulSpillState 4 := by
  apply evalWordStackMachine_longMul_spilled_preserves_other_value
    (config := longMulSpillConfig) (state := longMulSpillState)
    (final := ((wordStackLongMulInst longMulSpillConfig
      (.longMul 0 1 2 3)).bind
      (evalWordStackMachine longMulSpillState)).getD longMulSpillState)
    (destinationLeft := 0) (destinationRight := 1)
    (sourceLeft := 2) (sourceRight := 3) (other := 4)
    (destinationLeftSlot := 2) (destinationRightSlot := 3)
    (sourceLeftSlot := 4) (sourceRightSlot := 5)
    (otherLocation := .register 6)
  · simp [longMulSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulSpillConfig, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [longMulSpillConfig, longMulSpillState, wordStackLongMulInst,
      wordStackLongMulLocationsSafe, wordStackLongMulLocationSafe,
      wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
      wordStackJoin, wordStackLocation, wordStackOffset, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot, lookupNatInfo]

end Flapjack.RiscV
