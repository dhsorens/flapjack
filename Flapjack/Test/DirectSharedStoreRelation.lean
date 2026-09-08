import Flapjack.RiscV.CorrectnessDirectSharedStore
import Flapjack.Test.SharedLoadSpillRelation

/-! Regression coverage for public shared-memory stores with spilled addresses. -/

namespace Flapjack.RiscV

example :
    wordStackMappedValues sharedLoadSpillConfig sharedLoadSpillValues
      (((wordToStackProg (α := Nat) sharedLoadSpillConfig
        (.shareInst .store 3 (.var 2))).bind
        (evalWordStackMachine sharedLoadSpillState)).getD sharedLoadSpillState) := by
  apply evalWordStackMachine_direct_shared_store_preserves_mapped_values
    (config := sharedLoadSpillConfig) (state := sharedLoadSpillState)
    (final := ((wordToStackProg (α := Nat) sharedLoadSpillConfig
      (.shareInst .store 3 (.var 2))).bind
      (evalWordStackMachine sharedLoadSpillState)).getD sharedLoadSpillState)
    (source := 3) (address := 2)
    (sourceLocation := .register 6) (addressLocation := .stack 1)
    (values := sharedLoadSpillValues)
  · simp [sharedLoadSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [sharedLoadSpillConfig, wordStackLocation, lookupNatInfo]
  · exact by
      intro name value location hvalue hlocation
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
      intro name value location hvalue hlocation
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
      intro name value location hvalue hlocation
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
      wordStackSharedMemoryInst, wordStackSharedStoreInst, wordStackLocation,
      wordStackOffset, evalWordStackMachine, wordStackMachineWriteRegister,
      wordStackMachineWriteSharedMemory, lookupNatInfo]

end Flapjack.RiscV
