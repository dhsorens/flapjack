import Flapjack.RiscV.CorrectnessSpill

/-! Regression coverage for mixed register/stack move preservation. -/

namespace Flapjack.RiscV

def spillMoveConfig : WordStackConfig :=
  { locations := [(1, .register 5), (2, .register 6), (3, .stack 0)]
    scratch := 31
    stackBase := 8 }

def spillMoveState : WordStackMachineState 8 :=
  { registers := fun _ => 0
    stack := fun slot => if slot = 8 then BitVec.ofNat 8 17 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def spillMoveValues : Nat → Option (Word 8)
  | 3 => some (BitVec.ofNat 8 17)
  | _ => none

example :
    wordStackMachineValue spillMoveConfig
      (wordStackMachineWriteRegister spillMoveState 5 0) 3 =
      wordStackMachineValue spillMoveConfig spillMoveState 3 := by
  apply evalWordStackMachine_move_preserves_other_value
    (config := spillMoveConfig)
    (state := spillMoveState)
    (final := wordStackMachineWriteRegister spillMoveState 5 0)
    (destination := 1) (source := 2) (other := 3)
    (destinationLocation := .register 5)
    (sourceLocation := .register 6)
    (otherLocation := .stack 0)
  · simp [spillMoveConfig, wordStackLocation, lookupNatInfo]
  · simp [spillMoveConfig, wordStackLocation, lookupNatInfo]
  · simp [spillMoveConfig, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · decide
  · decide
  · simp [spillMoveConfig, spillMoveState, wordStackMove,
      wordStackLocation, lookupNatInfo, wordStackOffset,
      evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineBinOp]

example :
    wordStackMappedValues spillMoveConfig spillMoveValues spillMoveState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 3
  · subst name
    simp [spillMoveValues] at hvalue
    subst value
    simp [spillMoveConfig, spillMoveState, wordStackLocation,
      wordStackMachineValue, wordStackOffset, lookupNatInfo]
  · simp [spillMoveValues] at hvalue

example :
    wordStackMappedValuesExcept spillMoveConfig 1 spillMoveValues
      (wordStackMachineWriteRegister spillMoveState 5 0) := by
  apply evalWordStackMachine_move_preserves_unrelated_values
    (config := spillMoveConfig)
    (state := spillMoveState)
    (final := wordStackMachineWriteRegister spillMoveState 5 0)
    (destination := 1) (source := 2)
    (destinationLocation := .register 5)
    (sourceLocation := .register 6)
    (values := spillMoveValues)
  · simp [spillMoveConfig, wordStackLocation, lookupNatInfo]
  · simp [spillMoveConfig, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [spillMoveValues] at hvalue
        subst value
        simp [spillMoveConfig, wordStackLocation, lookupNatInfo,
          wordStackMachineValue, wordStackOffset, spillMoveState]
      · simp [spillMoveValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        have hlocation' : location = .stack 0 := by
          simpa [spillMoveConfig, wordStackLocation, lookupNatInfo] using hlocation.symm
        subst location
        decide
      · simp [spillMoveValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        have hlocation' : location = .stack 0 := by
          simpa [spillMoveConfig, wordStackLocation, lookupNatInfo] using hlocation.symm
        subst location
        decide
      · simp [spillMoveValues] at hvalue
  · simp [spillMoveConfig, spillMoveState, wordStackMove,
      wordStackLocation, lookupNatInfo, wordStackOffset,
      evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineBinOp]

end Flapjack.RiscV
