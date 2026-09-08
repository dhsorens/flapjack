import Flapjack.RiscV.CorrectnessLongMulMixed

/-! Regression coverage for mixed-source spilled-destination LongMul. -/

namespace Flapjack.RiscV

def longMulMixedConfig : WordStackConfig :=
  { locations := [(0, .stack 2), (1, .stack 3),
      (2, .register 6), (3, .stack 4), (4, .register 8)]
    scratch := 31
    stackBase := 10
    addressScratch := 29
    specialScratch := 28
    carryScratch := 27 }

def longMulMixedState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then 3 else if register = 8 then 23 else 0
    stack := fun offset => if offset = 16 then 4 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

example :
    wordStackMachineValue longMulMixedConfig
      (((wordStackLongMulInst longMulMixedConfig
        (.longMul 0 1 2 3)).bind
        (evalWordStackMachine longMulMixedState)).getD longMulMixedState) 4 =
      wordStackMachineValue longMulMixedConfig longMulMixedState 4 := by
  apply evalWordStackMachine_longMul_stackDest_preserves_other_value
    (config := longMulMixedConfig) (state := longMulMixedState)
    (final := ((wordStackLongMulInst longMulMixedConfig
      (.longMul 0 1 2 3)).bind
      (evalWordStackMachine longMulMixedState)).getD longMulMixedState)
    (destinationLeft := 0) (destinationRight := 1)
    (sourceLeft := 2) (sourceRight := 3) (other := 4)
    (destinationLeftSlot := 2) (destinationRightSlot := 3)
    (sourceLeftLocation := .register 6) (sourceRightLocation := .stack 4)
    (otherLocation := .register 8)
  · simp [longMulMixedConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulMixedConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulMixedConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulMixedConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulMixedConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulMixedConfig, wordStackLongMulLocationsSafe,
      wordStackLongMulLocationSafe, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [longMulMixedConfig]
  · simp [longMulMixedConfig, longMulMixedState, wordStackLongMulInst,
      wordStackLongMulLocationsSafe, wordStackLongMulLocationSafe,
      wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
      wordStackJoin, wordStackLocation, wordStackOffset, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot, lookupNatInfo]

end Flapjack.RiscV
