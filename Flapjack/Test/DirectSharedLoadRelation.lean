import Flapjack.RiscV.CorrectnessDirectSharedLoad
import Flapjack.Test.SharedLoadSpillRelation

/-! Regression coverage for public shared-memory loads through a spilled address. -/

namespace Flapjack.RiscV

example :
    wordStackMappedValuesExcept sharedLoadSpillConfig 1 sharedLoadSpillValues
      (((wordToStackProg (α := Nat) sharedLoadSpillConfig
        (.shareInst .load 1 (.var 2))).bind
        (evalWordStackMachine sharedLoadSpillState)).getD sharedLoadSpillState) := by
  apply evalWordStackMachine_direct_shared_load_preserves_unrelated_values
    (config := sharedLoadSpillConfig) (state := sharedLoadSpillState)
    (final := ((wordToStackProg (α := Nat) sharedLoadSpillConfig
      (.shareInst .load 1 (.var 2))).bind
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
  · simp [sharedLoadSpillConfig, sharedLoadSpillState, wordToStackProg,
      wordStackSharedMemoryInst, wordStackSharedLoadInst, wordStackLocation,
      wordStackOffset, evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineWriteSlot, lookupNatInfo]

end Flapjack.RiscV
