import Flapjack.RiscV.CorrectnessGetSpill

/-! Regression coverage for direct `get` with a spilled destination. -/

namespace Flapjack.RiscV

def getSpillConfig : WordStackConfig :=
  { locations := [(1, .stack 0), (2, .register 6)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def getSpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun _ => 0
    stores := fun store => if store = .currHeap then BitVec.ofNat 8 99 else 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def getSpillValues : Nat → Option (Word 8)
  | 2 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues getSpillConfig getSpillValues getSpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 2
  · subst name
    simp [getSpillValues] at hvalue
    subst value
    simp [getSpillConfig, getSpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [getSpillValues] at hvalue

example :
    wordStackMappedValuesExcept getSpillConfig 1 getSpillValues
      (((wordStackGet getSpillConfig 1 (.currHeap)).bind
        (evalWordStackMachine getSpillState)).getD getSpillState) := by
  apply evalWordStackMachine_get_preserves_unrelated_values
    (config := getSpillConfig)
    (state := getSpillState)
    (final := ((wordStackGet getSpillConfig 1 (.currHeap)).bind
      (evalWordStackMachine getSpillState)).getD getSpillState)
    (destination := 1) (store := .currHeap) (stackStore := .currHeap)
    (destinationLocation := .stack 0) (values := getSpillValues)
  · simp [getSpillConfig, wordStackLocation, lookupNatInfo]
  · decide
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 2
      · subst name
        simp [getSpillValues] at hvalue
        subst value
        simp [getSpillConfig, getSpillState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [getSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 2
      · subst name
        simp [getSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [getSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [getSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 2
      · subst name
        simp [getSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [getSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [getSpillValues] at hvalue
  · simp [getSpillConfig, getSpillState, wordStackGet, wordStackStoreName,
      wordStackJoin, evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, wordStackLocation, wordStackOffset,
      lookupNatInfo]

end Flapjack.RiscV
