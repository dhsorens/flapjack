import Flapjack.RiscV.CorrectnessLongMulRegister

/-! Regression coverage for register-resident LongMul lowering. -/

namespace Flapjack.RiscV

def longMulRegisterConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .register 5),
      (2, .register 6), (3, .register 7), (4, .register 8)]
    scratch := 31
    stackBase := 10
    addressScratch := 29
    specialScratch := 28
    carryScratch := 27 }

def longMulRegisterState : WordStackMachineState 8 :=
  { registers := fun register =>
      if register = 8 then BitVec.ofNat 8 23
      else if register = 6 then BitVec.ofNat 8 3
      else if register = 7 then BitVec.ofNat 8 4 else 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

example :
    wordStackMachineValue longMulRegisterConfig
      (((wordStackLongMulInst longMulRegisterConfig
        (.longMul 0 1 2 3)).bind
        (evalWordStackMachine longMulRegisterState)).getD longMulRegisterState) 4 =
      wordStackMachineValue longMulRegisterConfig longMulRegisterState 4 := by
  apply evalWordStackMachine_longMul_register_preserves_other_value
    (config := longMulRegisterConfig) (state := longMulRegisterState)
    (final := ((wordStackLongMulInst longMulRegisterConfig
      (.longMul 0 1 2 3)).bind
      (evalWordStackMachine longMulRegisterState)).getD longMulRegisterState)
    (destinationLeft := 0) (destinationRight := 1)
    (sourceLeft := 2) (sourceRight := 3) (other := 4)
    (destinationLeftRegister := 4) (destinationRightRegister := 5)
    (sourceLeftRegister := 6) (sourceRightRegister := 7) (otherRegister := 8)
  · simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulRegisterConfig, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · decide
  · simp [longMulRegisterConfig, longMulRegisterState, wordStackLongMulInst,
      wordStackLongMulLocationsSafe, wordStackLongMulLocationSafe,
      wordStackLocation, lookupNatInfo, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineValue]

end Flapjack.RiscV
