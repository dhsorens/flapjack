import Flapjack.RiscV.CorrectnessSetSpill

/-! Regression coverage for Set with a spilled source. -/

namespace Flapjack.RiscV

def setSpillConfig : WordStackConfig :=
  { locations := [(1, .stack 0), (2, .stack 1), (3, .register 6)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def setSpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset => if offset = 9 then BitVec.ofNat 8 17 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def setSpillValues : Nat → Option (Word 8)
  | 3 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues setSpillConfig setSpillValues setSpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 3
  · subst name
    simp [setSpillValues] at hvalue
    subst value
    simp [setSpillConfig, setSpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [setSpillValues] at hvalue

example :
    wordStackMappedValues setSpillConfig setSpillValues
      (((wordStackSetNat setSpillConfig .currHeap (.var 2)).bind
        (evalWordStackMachine setSpillState)).getD setSpillState) := by
  apply evalWordStackMachine_set_preserves_mapped_values
    (config := setSpillConfig)
    (state := setSpillState)
    (final := ((wordStackSetNat setSpillConfig .currHeap (.var 2)).bind
      (evalWordStackMachine setSpillState)).getD setSpillState)
    (store := .currHeap) (source := 2)
    (sourceLocation := .stack 1) (stackStore := .currHeap)
    (values := setSpillValues)
  · simp [setSpillConfig, wordStackLocation, lookupNatInfo]
  · decide
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [setSpillValues] at hvalue
        subst value
        simp [setSpillConfig, setSpillState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [setSpillValues] at hvalue
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [setSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [setSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [setSpillValues] at hvalue
  · simp [setSpillConfig, setSpillState, wordStackSetNat,
      wordStackStoreNameNat, wordStackAtomNat, wordStackReadRegister,
      wordStackLocation, wordStackOffset, wordStackJoin, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineWriteStore, lookupNatInfo]

end Flapjack.RiscV
