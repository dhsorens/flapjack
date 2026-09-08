import Flapjack.RiscV.CorrectnessDirectDiv

/-! Regression coverage for public arithmetic division with spilled operands. -/

namespace Flapjack.RiscV

def directDivConfig : WordStackConfig :=
  { locations := [(1, .stack 0), (2, .stack 1), (3, .stack 2),
      (4, .register 6)]
    scratch := 31
    stackBase := 8
    addressScratch := 29 }

def directDivState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset =>
      if offset = 9 then BitVec.ofNat 8 40
      else if offset = 10 then BitVec.ofNat 8 5 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def directDivValues : Nat → Option (Word 8)
  | 4 => some (BitVec.ofNat 8 23)
  | _ => none

example :
    wordStackMappedValues directDivConfig directDivValues directDivState := by
  intro name value location hvalue hlocation
  by_cases hname : name = 4
  · subst name
    simp [directDivValues] at hvalue
    subst value
    simp [directDivConfig, directDivState, wordStackMachineValue,
      wordStackLocation, wordStackOffset, lookupNatInfo]
  · simp [directDivValues] at hvalue

example :
    wordStackMappedValuesExcept directDivConfig 1 directDivValues
      (((wordToStackProg (α := Nat) directDivConfig
        (.inst (.arith (.div 1 2 3)))).bind
        (evalWordStackMachine directDivState)).getD directDivState) := by
  apply evalWordStackMachine_direct_div_preserves_unrelated_values
    (config := directDivConfig) (state := directDivState)
    (final := ((wordToStackProg (α := Nat) directDivConfig
      (.inst (.arith (.div 1 2 3)))).bind
      (evalWordStackMachine directDivState)).getD directDivState)
    (destination := 1) (dividend := 2) (divisor := 3)
    (destinationLocation := .stack 0)
    (dividendLocation := .stack 1) (divisorLocation := .stack 2)
    (values := directDivValues)
  · simp [directDivConfig, wordStackLocation, lookupNatInfo]
  · simp [directDivConfig, wordStackLocation, lookupNatInfo]
  · simp [directDivConfig, wordStackLocation, lookupNatInfo]
  · decide
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [directDivValues] at hvalue
        subst value
        simp [directDivConfig, directDivState, wordStackMachineValue,
          wordStackLocation, wordStackOffset, lookupNatInfo]
      · simp [directDivValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [directDivValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [directDivConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [directDivValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [directDivValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [directDivConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [directDivValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 4
      · subst name
        simp [directDivValues] at hvalue
        subst value
        have hlocation' : location = .register 6 := by
          simpa [directDivConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [directDivValues] at hvalue
  · simp [directDivConfig, directDivState, wordToStackProg,
      wordToStackInst, wordStackArithInst, wordStackDivInst,
      wordStackLocation, wordStackOffset, wordStackJoin, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      wordSpecialArithLocationsSafe,
      lookupNatInfo]

end Flapjack.RiscV
