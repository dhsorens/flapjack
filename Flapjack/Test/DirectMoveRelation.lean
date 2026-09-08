import Flapjack.RiscV.CorrectnessDirectMove
import Flapjack.Test.SpillRelation

/-! Regression coverage for public variable moves with mapped spilled values. -/

namespace Flapjack.RiscV

example :
    wordStackMappedValuesExcept spillMoveConfig 1 spillMoveValues
      (((wordToStackProg (α := Nat) spillMoveConfig
        (.assign 1 (.var 2))).bind
        (evalWordStackMachine spillMoveState)).getD spillMoveState) := by
  apply evalWordStackMachine_direct_assign_preserves_unrelated_values
    (config := spillMoveConfig) (state := spillMoveState)
    (final := ((wordToStackProg (α := Nat) spillMoveConfig
      (.assign 1 (.var 2))).bind
      (evalWordStackMachine spillMoveState)).getD spillMoveState)
    (destination := 1) (source := 2)
    (destinationLocation := .register 5) (sourceLocation := .register 6)
    (values := spillMoveValues)
  · simp [spillMoveConfig, wordStackLocation, lookupNatInfo]
  · simp [spillMoveConfig, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [spillMoveValues] at hvalue
        subst value
        simp [spillMoveConfig, spillMoveState, wordStackLocation,
          wordStackMachineValue, wordStackOffset, lookupNatInfo]
      · simp [spillMoveValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        have hlocation' : location = .stack 0 := by
          simpa [spillMoveConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [spillMoveValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        have hlocation' : location = .stack 0 := by
          simpa [spillMoveConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [spillMoveValues] at hvalue
  · simp [spillMoveConfig, spillMoveState, wordToStackProg, wordStackMove,
      wordStackLocation, wordStackOffset, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineBinOp, lookupNatInfo]

example :
    wordStackMappedValuesExcept spillMoveConfig 1 spillMoveValues
      (((wordToStackProg (α := Nat) spillMoveConfig
        (.locValue 1 2)).bind
        (evalWordStackMachine spillMoveState)).getD spillMoveState) := by
  apply evalWordStackMachine_direct_locValue_preserves_unrelated_values
    (config := spillMoveConfig) (state := spillMoveState)
    (final := ((wordToStackProg (α := Nat) spillMoveConfig
      (.locValue 1 2)).bind
      (evalWordStackMachine spillMoveState)).getD spillMoveState)
    (destination := 1) (source := 2)
    (destinationLocation := .register 5) (sourceLocation := .register 6)
    (values := spillMoveValues)
  · simp [spillMoveConfig, wordStackLocation, lookupNatInfo]
  · simp [spillMoveConfig, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · exact by
      intro name value location hvalue hlocation
      by_cases hother : name = 3
      · subst name
        simp [spillMoveValues] at hvalue
        subst value
        simp [spillMoveConfig, spillMoveState, wordStackLocation,
          wordStackMachineValue, wordStackOffset, lookupNatInfo]
      · simp [spillMoveValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        have hlocation' : location = .stack 0 := by
          simpa [spillMoveConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [spillMoveValues] at hvalue
  · exact by
      intro name value location hname hvalue hlocation
      by_cases hother : name = 3
      · subst name
        have hlocation' : location = .stack 0 := by
          simpa [spillMoveConfig, wordStackLocation, lookupNatInfo] using
            hlocation.symm
        subst location
        decide
      · simp [spillMoveValues] at hvalue
  · simp [spillMoveConfig, spillMoveState, wordToStackProg, wordStackMove,
      wordStackLocation, wordStackOffset, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineBinOp, lookupNatInfo]

end Flapjack.RiscV
