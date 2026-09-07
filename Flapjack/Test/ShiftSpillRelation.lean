import Flapjack.RiscV.CorrectnessShiftSpill

/-! Regression coverage for shift lowering with two spilled operands. -/

namespace Flapjack.RiscV

def shiftSpillConfig : WordStackConfig :=
  { locations := [(1, .register 5), (2, .stack 0), (3, .stack 1),
      (4, .register 6)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def shiftSpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset =>
      if offset = 8 then BitVec.ofNat 8 17
      else if offset = 9 then BitVec.ofNat 8 2 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def shiftSpillValues : Nat → Option (Word 8)
  | 4 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues shiftSpillConfig shiftSpillValues shiftSpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 4
  · subst name
    simp [shiftSpillValues] at hvalue
    subst value
    simp [shiftSpillConfig, shiftSpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [shiftSpillValues] at hvalue

example :
    wordStackMappedValuesExcept shiftSpillConfig 1 shiftSpillValues
      (((wordStackCompileShiftNat shiftSpillConfig 1 .lsl
        (.var 2) (.var 3)).bind
        (evalWordStackMachine shiftSpillState)).getD shiftSpillState) := by
  apply evalWordStackMachine_shift_preserves_unrelated_values
    (config := shiftSpillConfig)
    (state := shiftSpillState)
    (final := ((wordStackCompileShiftNat shiftSpillConfig 1 .lsl
      (.var 2) (.var 3)).bind
      (evalWordStackMachine shiftSpillState)).getD shiftSpillState)
    (operator := .lsl) (destination := 1) (left := 2) (right := 3)
    (destinationLocation := .register 5)
    (leftLocation := .stack 0) (rightLocation := .stack 1)
    (values := shiftSpillValues)
  · simp [shiftSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [shiftSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [shiftSpillConfig, wordStackLocation, lookupNatInfo]
  · decide
  · exact by
      intro name value location hvalue hlocation
      by_cases hname : name = 4
      · subst name
        simp [shiftSpillValues] at hvalue
        subst value
        simp [shiftSpillConfig, shiftSpillState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [shiftSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [shiftSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [shiftSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [shiftSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [shiftSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [shiftSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [shiftSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [shiftSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [shiftSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [shiftSpillValues] at hvalue
  · simp [shiftSpillConfig, shiftSpillState, wordStackCompileShiftNat,
      wordStackAtomNat, wordStackWritePhysicalNat, wordStackReadRegister,
      wordStackLocation, wordStackOffset, wordStackJoin, evalWordStackMachine,
      wordStackMachineWriteRegister, lookupNatInfo]

end Flapjack.RiscV
