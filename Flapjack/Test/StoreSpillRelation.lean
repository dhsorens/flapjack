import Flapjack.RiscV.CorrectnessStoreSpill

/-! Regression coverage for storing through a spilled source. -/

namespace Flapjack.RiscV

def storeSpillConfig : WordStackConfig :=
  { locations := [(2, .stack 0), (3, .register 6), (4, .stack 1)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def storeSpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 100 else 0
    stack := fun offset =>
      if offset = 8 then BitVec.ofNat 8 17
      else if offset = 9 then BitVec.ofNat 8 23 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def storeSpillValues : Nat → Option (Word 8)
  | 4 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues storeSpillConfig storeSpillValues storeSpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 4
  · subst name
    simp [storeSpillValues] at hvalue
    subst value
    simp [storeSpillConfig, storeSpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [storeSpillValues] at hvalue

example :
    wordStackMappedValues storeSpillConfig storeSpillValues
      (((wordStackCompileStoreNat storeSpillConfig (.var 3) (.var 2)).bind
        (evalWordStackMachine storeSpillState)).getD storeSpillState) := by
  apply evalWordStackMachine_store_preserves_mapped_values
    (config := storeSpillConfig)
    (state := storeSpillState)
    (final := ((wordStackCompileStoreNat storeSpillConfig (.var 3) (.var 2)).bind
      (evalWordStackMachine storeSpillState)).getD storeSpillState)
    (source := 2) (address := 3)
    (sourceLocation := .stack 0) (addressLocation := .register 6)
    (values := storeSpillValues)
  · simp [storeSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [storeSpillConfig, wordStackLocation, lookupNatInfo]
  · decide
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [storeSpillValues] at hvalue
        subst value
        have hlocation' : location = .stack 1 := by
          simpa [storeSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [storeSpillValues] at hvalue
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [storeSpillValues] at hvalue
        subst value
        have hlocation' : location = .stack 1 := by
          simpa [storeSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [storeSpillValues] at hvalue
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [storeSpillValues] at hvalue
        subst value
        have hlocation' : location = .stack 1 := by
          simpa [storeSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [storeSpillValues] at hvalue
  · simp [storeSpillConfig, storeSpillState, wordStackCompileStoreNat,
      wordStackAtomNat, wordStackReadRegister, wordStackJoin,
      wordStackLocation, wordStackOffset, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineWriteMemory,
      lookupNatInfo]

end Flapjack.RiscV
