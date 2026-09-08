import Flapjack.RiscV.CorrectnessLookupSpill

/-! Regression coverage for a StackStore lookup into a spilled destination. -/

namespace Flapjack.RiscV

def lookupSpillConfig : WordStackConfig :=
  { locations := [(1, .stack 0), (2, .register 6)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def lookupSpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun _ => 0
    stores := fun store => if store = .currHeap then BitVec.ofNat 8 99 else 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def lookupSpillValues : Nat → Option (Word 8)
  | 2 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues lookupSpillConfig lookupSpillValues lookupSpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 2
  · subst name
    simp [lookupSpillValues] at hvalue
    subst value
    simp [lookupSpillConfig, lookupSpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [lookupSpillValues] at hvalue

example :
    wordStackMappedValuesExcept lookupSpillConfig 1 lookupSpillValues
      (((wordStackCompileExpNat lookupSpillConfig 1
        (.lookup .currHeap)).bind
        (evalWordStackMachine lookupSpillState)).getD lookupSpillState) := by
  apply evalWordStackMachine_lookup_preserves_unrelated_values
    (config := lookupSpillConfig)
    (state := lookupSpillState)
    (final := ((wordStackCompileExpNat lookupSpillConfig 1
      (.lookup .currHeap)).bind
      (evalWordStackMachine lookupSpillState)).getD lookupSpillState)
    (destination := 1) (store := .currHeap)
    (stackStore := .currHeap) (destinationLocation := .stack 0)
    (values := lookupSpillValues)
  · simp [lookupSpillConfig, wordStackLocation, lookupNatInfo]
  · decide
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 2
      · subst name
        simp [lookupSpillValues] at hvalue
        subst value
        simp [lookupSpillConfig, lookupSpillState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [lookupSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 2
      · subst name
        simp [lookupSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [lookupSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [lookupSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 2
      · subst name
        simp [lookupSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [lookupSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [lookupSpillValues] at hvalue
  · simp [lookupSpillConfig, lookupSpillState, wordStackCompileExpNat,
      wordStackStoreNameNat, wordStackWritePhysicalNat, wordStackLocation,
      wordStackOffset, wordStackJoin, evalWordStackMachine,
      wordStackMachineWriteRegister, lookupNatInfo]

end Flapjack.RiscV
