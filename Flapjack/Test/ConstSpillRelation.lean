import Flapjack.RiscV.CorrectnessConstSpill

/-! Regression coverage for constants written to a spilled destination. -/

namespace Flapjack.RiscV

def constSpillConfig : WordStackConfig :=
  { locations := [(1, .stack 0), (2, .register 6)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def constSpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun _ => 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def constSpillValues : Nat → Option (Word 8)
  | 2 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues constSpillConfig constSpillValues constSpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 2
  · subst name
    simp [constSpillValues] at hvalue
    subst value
    simp [constSpillConfig, constSpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [constSpillValues] at hvalue

example :
    wordStackMappedValuesExcept constSpillConfig 1 constSpillValues
      (((wordStackCompileExpNat constSpillConfig 1 (.const 17)).bind
        (evalWordStackMachine constSpillState)).getD constSpillState) := by
  apply evalWordStackMachine_const_preserves_unrelated_values
    (config := constSpillConfig)
    (state := constSpillState)
    (final := ((wordStackCompileExpNat constSpillConfig 1 (.const 17)).bind
      (evalWordStackMachine constSpillState)).getD constSpillState)
    (destination := 1) (value := 17)
    (destinationLocation := .stack 0)
    (values := constSpillValues)
  · simp [constSpillConfig, wordStackLocation, lookupNatInfo]
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 2
      · subst name
        simp [constSpillValues] at hvalue
        subst value
        simp [constSpillConfig, constSpillState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [constSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 2
      · subst name
        simp [constSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [constSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [constSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 2
      · subst name
        simp [constSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [constSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [constSpillValues] at hvalue
  · simp [constSpillConfig, constSpillState, wordStackCompileExpNat,
      wordStackWritePhysicalNat, wordStackLocation, wordStackOffset,
      wordStackJoin, evalWordStackMachine, wordStackMachineWriteRegister,
      lookupNatInfo]

end Flapjack.RiscV
