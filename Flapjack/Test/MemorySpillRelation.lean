import Flapjack.RiscV.CorrectnessMemorySpill

/-! Regression coverage for direct memory load/store spill lowering. -/

namespace Flapjack.RiscV

def memorySpillConfig : WordStackConfig :=
  { locations := [(1, .stack 0), (2, .stack 1), (3, .register 6)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def memorySpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset => if offset = 9 then BitVec.ofNat 8 17 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def memorySpillValues : Nat → Option (Word 8)
  | 3 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues memorySpillConfig memorySpillValues memorySpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 3
  · subst name
    simp [memorySpillValues] at hvalue
    subst value
    simp [memorySpillConfig, memorySpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [memorySpillValues] at hvalue

example :
    wordStackMappedValuesExcept memorySpillConfig 1 memorySpillValues
      (((wordStackMemoryInst memorySpillConfig .load 1 2).bind
        (evalWordStackMachine memorySpillState)).getD memorySpillState) := by
  apply evalWordStackMachine_memory_load_preserves_unrelated_values
    (config := memorySpillConfig) (state := memorySpillState)
    (final := ((wordStackMemoryInst memorySpillConfig .load 1 2).bind
      (evalWordStackMachine memorySpillState)).getD memorySpillState)
    (destination := 1) (address := 2) (destinationLocation := .stack 0)
    (addressLocation := .stack 1) (values := memorySpillValues)
  · simp [memorySpillConfig, wordStackLocation, lookupNatInfo]
  · simp [memorySpillConfig, wordStackLocation, lookupNatInfo]
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        simp [memorySpillConfig, memorySpillState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [memorySpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · simp [memorySpillConfig, memorySpillState, wordStackMemoryInst,
      wordStackLoadInst, wordStackLocation, wordStackOffset,
      evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, lookupNatInfo]

example :
    wordStackMappedValues memorySpillConfig memorySpillValues
      (((wordStackMemoryInst memorySpillConfig .store 2 3).bind
        (evalWordStackMachine memorySpillState)).getD memorySpillState) := by
  apply evalWordStackMachine_memory_store_preserves_mapped_values
    (config := memorySpillConfig) (state := memorySpillState)
    (final := ((wordStackMemoryInst memorySpillConfig .store 2 3).bind
      (evalWordStackMachine memorySpillState)).getD memorySpillState)
    (source := 2) (address := 3) (sourceLocation := .stack 1)
    (addressLocation := .register 6) (values := memorySpillValues)
  · simp [memorySpillConfig, wordStackLocation, lookupNatInfo]
  · simp [memorySpillConfig, wordStackLocation, lookupNatInfo]
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [memorySpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [memorySpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [memorySpillValues] at hvalue
  · simp [memorySpillConfig, memorySpillState, wordStackMemoryInst,
      wordStackStoreInst, wordStackLocation, wordStackOffset,
      evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineWriteMemory, lookupNatInfo]

end Flapjack.RiscV
