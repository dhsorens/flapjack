import Flapjack.RiscV.CorrectnessDirectAddCarry
import Flapjack.Test.AddCarrySpillRelation

/-! Regression coverage for public fully spilled AddCarry lowering. -/

namespace Flapjack.RiscV

example :
    ∀ name value location, name ≠ 0 → name ≠ 1 →
      addCarrySpillValues name = some value →
      wordStackLocation addCarrySpillConfig name = some location →
      wordStackMachineValue addCarrySpillConfig
        (((wordToStackProg (α := Nat) addCarrySpillConfig
          (.inst (.arith (.addCarry 0 1 2 3 4)))).bind
          (evalWordStackMachine addCarrySpillState)).getD addCarrySpillState)
        name = some value := by
  apply evalWordStackMachine_direct_addCarry_spilled_preserves_unrelated_values
    (config := addCarrySpillConfig) (state := addCarrySpillState)
    (final := ((wordToStackProg (α := Nat) addCarrySpillConfig
      (.inst (.arith (.addCarry 0 1 2 3 4)))).bind
      (evalWordStackMachine addCarrySpillState)).getD addCarrySpillState)
    (destination := 0) (resultCarry := 1) (sourceLeft := 2)
    (sourceRight := 3) (carryIn := 4)
    (destinationSlot := 2) (resultCarrySlot := 3)
    (sourceLeftSlot := 4) (sourceRightSlot := 5) (carryInSlot := 6)
    (values := addCarrySpillValues)
  all_goals try simp [addCarrySpillConfig, wordStackLocation, lookupNatInfo]
  · decide
  · intro name value location hvalue hlocation
    by_cases hother : name = 5
    · subst name
      simp [addCarrySpillValues] at hvalue
      subst value
      have hlocation' : location = .register 6 := by
        simpa [addCarrySpillConfig, wordStackLocation, lookupNatInfo] using
          hlocation.symm
      subst location
      decide
    · simp [addCarrySpillValues] at hvalue
  · intro name value location hname hresult hvalue hlocation
    by_cases hother : name = 5
    · subst name
      simp [addCarrySpillValues] at hvalue
      subst value
      have hlocation' : location = .register 6 := by
        simpa [addCarrySpillConfig, wordStackLocation, lookupNatInfo] using
          hlocation.symm
      subst location
      decide
    · simp [addCarrySpillValues] at hvalue
  · intro name value location hname hresult hvalue hlocation
    by_cases hother : name = 5
    · subst name
      simp [addCarrySpillValues] at hvalue
      subst value
      have hlocation' : location = .register 6 := by
        simpa [addCarrySpillConfig, wordStackLocation, lookupNatInfo] using
          hlocation.symm
      subst location
      decide
    · simp [addCarrySpillValues] at hvalue
  · intro name value location hname hresult hvalue hlocation
    by_cases hother : name = 5
    · subst name
      simp [addCarrySpillValues] at hvalue
      subst value
      have hlocation' : location = .register 6 := by
        simpa [addCarrySpillConfig, wordStackLocation, lookupNatInfo] using
          hlocation.symm
      subst location
      decide
    · simp [addCarrySpillValues] at hvalue
  · intro name value location hname hresult hvalue hlocation
    by_cases hother : name = 5
    · subst name
      simp [addCarrySpillValues] at hvalue
      subst value
      have hlocation' : location = .register 6 := by
        simpa [addCarrySpillConfig, wordStackLocation, lookupNatInfo] using
          hlocation.symm
      subst location
      decide
    · simp [addCarrySpillValues] at hvalue
  · intro name value location hname hresult hvalue hlocation
    by_cases hother : name = 5
    · subst name
      simp [addCarrySpillValues] at hvalue
      subst value
      have hlocation' : location = .register 6 := by
        simpa [addCarrySpillConfig, wordStackLocation, lookupNatInfo] using
          hlocation.symm
      subst location
      decide
    · simp [addCarrySpillValues] at hvalue
  · intro name value location hname hresult hvalue hlocation
    by_cases hother : name = 5
    · subst name
      simp [addCarrySpillValues] at hvalue
      subst value
      have hlocation' : location = .register 6 := by
        simpa [addCarrySpillConfig, wordStackLocation, lookupNatInfo] using
          hlocation.symm
      subst location
      decide
    · simp [addCarrySpillValues] at hvalue
  · have hcompiled :
        wordToStackProg (α := Nat) addCarrySpillConfig
          (.inst (.arith (.addCarry 0 1 2 3 4))) =
          some (.seq (.stackLoad 29 14)
            (.seq (.stackLoad 28 15)
              (.seq (.stackLoad 27 16)
                (.seq (.inst (.arith (.addCarry 27 28 29 28 27)))
                  (.seq (.stackStore 27 12) (.stackStore 28 13))))) :
            StackProg Nat) := by
      simp [addCarrySpillConfig, wordToStackProg, wordToStackInst,
        wordStackArithInst, wordStackAddCarryInst,
        wordStackAddCarryLocationSafe, wordStackLongMulMoveToPhysical,
        wordStackLongMulMoveFromPhysical, wordStackJoin, wordStackLocation,
        wordStackOffset, wordSpecialArithLocationsSafe, lookupNatInfo]
    simp only [addCarrySpillConfig] at hcompiled ⊢
    rw [hcompiled]
    simp [addCarrySpillState, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot,
      ]

end Flapjack.RiscV
