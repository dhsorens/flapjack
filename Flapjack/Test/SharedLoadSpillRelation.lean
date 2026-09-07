import Flapjack.RiscV.CorrectnessSharedLoadSpill

/-! Regression coverage for shared loads through a spilled address. -/

namespace Flapjack.RiscV

def sharedLoadSpillConfig : WordStackConfig :=
  { locations := [(1, .stack 0), (2, .stack 1), (3, .register 6)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def sharedLoadSpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset => if offset = 9 then BitVec.ofNat 8 17 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun address =>
      if address = BitVec.ofNat 8 17 then 42 else 0 }

def sharedLoadSpillValues : Nat → Option (Word 8)
  | 3 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues sharedLoadSpillConfig sharedLoadSpillValues
      sharedLoadSpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 3
  · subst name
    simp [sharedLoadSpillValues] at hvalue
    subst value
    simp [sharedLoadSpillConfig, sharedLoadSpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [sharedLoadSpillValues] at hvalue

example :
    wordStackMappedValuesExcept sharedLoadSpillConfig 1 sharedLoadSpillValues
      (((wordStackCompileSharedNat sharedLoadSpillConfig .load 1 (.var 2)).bind
        (evalWordStackMachine sharedLoadSpillState)).getD sharedLoadSpillState) := by
  apply evalWordStackMachine_shared_load_preserves_unrelated_values
    (config := sharedLoadSpillConfig)
    (state := sharedLoadSpillState)
    (final := ((wordStackCompileSharedNat sharedLoadSpillConfig .load 1
      (.var 2)).bind
      (evalWordStackMachine sharedLoadSpillState)).getD sharedLoadSpillState)
    (destination := 1) (address := 2)
    (destinationLocation := .stack 0) (addressLocation := .stack 1)
    (values := sharedLoadSpillValues)
  · simp [sharedLoadSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [sharedLoadSpillConfig, wordStackLocation, lookupNatInfo]
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [sharedLoadSpillValues] at hvalue
        subst value
        simp [sharedLoadSpillConfig, sharedLoadSpillState,
          wordStackMachineValue, wordStackLocation, wordStackOffset,
          lookupNatInfo]
      · simp [sharedLoadSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [sharedLoadSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [sharedLoadSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [sharedLoadSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [sharedLoadSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [sharedLoadSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [sharedLoadSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [sharedLoadSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [sharedLoadSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [sharedLoadSpillValues] at hvalue
  · simp [sharedLoadSpillConfig, sharedLoadSpillState,
      wordStackCompileSharedNat, wordStackAtomNat, wordStackWritePhysicalNat,
      wordStackReadRegister, wordStackLocation, wordStackOffset, wordStackJoin,
      evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, lookupNatInfo]

end Flapjack.RiscV
