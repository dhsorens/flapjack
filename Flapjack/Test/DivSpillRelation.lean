import Flapjack.RiscV.CorrectnessDivSpill

/-! Regression coverage for division with a fully spilled operand triple. -/

namespace Flapjack.RiscV

def divSpillConfig : WordStackConfig :=
  { locations := [(1, .stack 0), (2, .stack 1), (3, .stack 2),
      (4, .register 6)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def divSpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset =>
      if offset = 9 then BitVec.ofNat 8 40
      else if offset = 10 then BitVec.ofNat 8 5 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def divSpillValues : Nat → Option (Word 8)
  | 4 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues divSpillConfig divSpillValues divSpillState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 4
  · subst name
    simp [divSpillValues] at hvalue
    subst value
    simp [divSpillConfig, divSpillState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [divSpillValues] at hvalue

example :
    wordStackMappedValuesExcept divSpillConfig 1 divSpillValues
      (((wordStackDivInst divSpillConfig 1 2 3).bind
        (evalWordStackMachine divSpillState)).getD divSpillState) := by
  apply evalWordStackMachine_div_preserves_unrelated_values
    (config := divSpillConfig)
    (state := divSpillState)
    (final := ((wordStackDivInst divSpillConfig 1 2 3).bind
      (evalWordStackMachine divSpillState)).getD divSpillState)
    (destination := 1) (dividend := 2) (divisor := 3)
    (destinationLocation := .stack 0)
    (dividendLocation := .stack 1) (divisorLocation := .stack 2)
    (values := divSpillValues)
  · simp [divSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [divSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [divSpillConfig, wordStackLocation, lookupNatInfo]
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [divSpillValues] at hvalue
        subst value
        simp [divSpillConfig, divSpillState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [divSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [divSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [divSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [divSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [divSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [divSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [divSpillValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [divSpillValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [divSpillConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [divSpillValues] at hvalue
  · simp [divSpillConfig, divSpillState, wordStackDivInst,
      wordStackLocation, wordStackOffset, wordStackJoin, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot, lookupNatInfo]

end Flapjack.RiscV
