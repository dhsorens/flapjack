import Flapjack.RiscV.CorrectnessLoadSpill

/-! Regression coverage for loading through a spilled address. -/

namespace Flapjack.RiscV

def loadSpillConfig : WordStackConfig :=
  { locations := [(1, .register 5), (2, .stack 0), (3, .register 6)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def loadSpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset => if offset = 8 then BitVec.ofNat 8 17 else 0
    stores := fun _ => 0
    memory := fun address => if address = BitVec.ofNat 8 17 then 42 else 0
    sharedMemory := fun _ => 0 }

def loadSpillValues : Nat → Option (Word 8)
  | 3 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues loadSpillConfig loadSpillValues loadSpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 3
  · subst name
    simp [loadSpillValues] at hvalue
    subst value
    simp [loadSpillConfig, loadSpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [loadSpillValues] at hvalue

example :
    wordStackMappedValuesExcept loadSpillConfig 1 loadSpillValues
      (((wordStackCompileLoadNat loadSpillConfig 1 (.var 2)).bind
        (evalWordStackMachine loadSpillState)).getD loadSpillState) := by
  apply evalWordStackMachine_load_preserves_unrelated_values
    (config := loadSpillConfig)
    (state := loadSpillState)
    (final := ((wordStackCompileLoadNat loadSpillConfig 1 (.var 2)).bind
      (evalWordStackMachine loadSpillState)).getD loadSpillState)
    (destination := 1) (address := 2)
    (destinationLocation := .register 5)
    (addressLocation := .stack 0)
    (values := loadSpillValues)
  · simp [loadSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [loadSpillConfig, wordStackLocation, lookupNatInfo]
  · exact by
      intro name value location hvalue hlocation
      by_cases hname : name = 3
      · subst name
        simp [loadSpillValues] at hvalue
        subst value
        simp [loadSpillConfig, loadSpillState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [loadSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [loadSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [loadSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [loadSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [loadSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [loadSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [loadSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [loadSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [loadSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [loadSpillValues] at hvalue
  · simp [loadSpillConfig, loadSpillState, wordStackCompileLoadNat,
      wordStackAtomNat, wordStackWritePhysicalNat, wordStackReadRegister,
      wordStackLocation, wordStackOffset, wordStackJoin, evalWordStackMachine,
      wordStackMachineWriteRegister, lookupNatInfo]

end Flapjack.RiscV
