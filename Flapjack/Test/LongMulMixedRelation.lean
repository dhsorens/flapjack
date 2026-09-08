import Flapjack.RiscV.CorrectnessDirectLongMulMixed

/-! Regression coverage for mixed-source spilled-destination LongMul. -/

namespace Flapjack.RiscV

def longMulMixedConfig : WordStackConfig :=
  { locations := [(0, .stack 2), (1, .stack 3),
      (2, .register 6), (3, .stack 4), (4, .register 8)]
    scratch := 31
    stackBase := 10
    addressScratch := 29
    specialScratch := 28
    carryScratch := 27 }

def longMulMixedState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then 3 else if register = 8 then 23 else 0
    stack := fun offset => if offset = 16 then 4 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def longMulMixedValues : Nat → Option (Word 8) := fun name =>
  if name = 4 then some (BitVec.ofNat 8 23) else none

example :
    wordStackMachineValue longMulMixedConfig
      (((wordStackLongMulInst longMulMixedConfig
        (.longMul 0 1 2 3)).bind
        (evalWordStackMachine longMulMixedState)).getD longMulMixedState) 4 =
      wordStackMachineValue longMulMixedConfig longMulMixedState 4 := by
  apply evalWordStackMachine_longMul_stackDest_preserves_other_value
    (config := longMulMixedConfig) (state := longMulMixedState)
    (final := ((wordStackLongMulInst longMulMixedConfig
      (.longMul 0 1 2 3)).bind
      (evalWordStackMachine longMulMixedState)).getD longMulMixedState)
    (destinationLeft := 0) (destinationRight := 1)
    (sourceLeft := 2) (sourceRight := 3) (other := 4)
    (destinationLeftSlot := 2) (destinationRightSlot := 3)
    (sourceLeftLocation := .register 6) (sourceRightLocation := .stack 4)
    (otherLocation := .register 8)
  · simp [longMulMixedConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulMixedConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulMixedConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulMixedConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulMixedConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulMixedConfig, wordStackLongMulLocationsSafe,
      wordStackLongMulLocationSafe, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [longMulMixedConfig]
  · simp [longMulMixedConfig, longMulMixedState, wordStackLongMulInst,
      wordStackLongMulLocationsSafe, wordStackLongMulLocationSafe,
      wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
      wordStackJoin, wordStackLocation, wordStackOffset, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot, lookupNatInfo]

example :
    ∀ name value location, name ≠ 0 → name ≠ 1 →
      longMulMixedValues name = some value →
      wordStackLocation longMulMixedConfig name = some location →
      wordStackMachineValue longMulMixedConfig
        (((wordToStackProg (α := Nat) longMulMixedConfig
          (.inst (.arith (.longMul 0 1 2 3)))).bind
          (evalWordStackMachine longMulMixedState)).getD longMulMixedState)
        name = some value := by
  have hvalue_location : ∀ name value location,
      longMulMixedValues name = some value →
      wordStackLocation longMulMixedConfig name = some location →
      name = 4 ∧ value = BitVec.ofNat 8 23 ∧ location = .register 8 := by
    intro name value location hvalue hlocation
    simp [longMulMixedValues] at hvalue
    by_cases hname : name = 4
    · subst name
      simp at hvalue
      subst value
      have hlocation' : location = .register 8 := by
        simpa [longMulMixedConfig, wordStackLocation, lookupNatInfo] using
          hlocation.symm
      exact ⟨rfl, rfl, hlocation'⟩
    · simp [hname] at hvalue
  refine evalWordStackMachine_direct_longMul_stackDest_preserves_unrelated_values
    (config := longMulMixedConfig) (state := longMulMixedState)
    (final := ((wordToStackProg (α := Nat) longMulMixedConfig
      (.inst (.arith (.longMul 0 1 2 3)))).bind
      (evalWordStackMachine longMulMixedState)).getD longMulMixedState)
    (destinationLeft := 0) (destinationRight := 1)
    (sourceLeft := 2) (sourceRight := 3)
    (destinationLeftSlot := 2) (destinationRightSlot := 3)
    (sourceLeftLocation := .register 6) (sourceRightLocation := .stack 4)
    (values := longMulMixedValues)
    (hdestinationLeft := by simp [longMulMixedConfig, wordStackLocation, lookupNatInfo])
    (hdestinationRight := by simp [longMulMixedConfig, wordStackLocation, lookupNatInfo])
    (hsourceLeft := by simp [longMulMixedConfig, wordStackLocation, lookupNatInfo])
    (hsourceRight := by simp [longMulMixedConfig, wordStackLocation, lookupNatInfo])
    (hspecial := by simp [longMulMixedConfig, wordSpecialArithLocationsSafe,
      lookupNatInfo])
    (hsafe := by simp [longMulMixedConfig, wordStackLongMulLocationsSafe,
      wordStackLongMulLocationSafe, wordStackLocation, lookupNatInfo])
    (hreserved := by decide)
    (hvalues := by
      intro name value location hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      simp [longMulMixedConfig, longMulMixedState, wordStackMachineValue,
        wordStackLocation, wordStackOffset, lookupNatInfo])
    (hnoaliasLeft := by
      intro name value location hname hright hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      decide)
    (hnoaliasRight := by
      intro name value location hname hright hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      decide)
    (hno_scratch := by
      intro name value location hname hright hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      decide)
    (hno_addressScratch := by
      intro name value location hname hright hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      decide)
    (hno_specialScratch := by
      intro name value location hname hright hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      decide)
    (heval := by
      simp [longMulMixedConfig, longMulMixedState, wordToStackProg,
        wordToStackInst, wordStackArithInst, wordStackLongMulInst,
        wordStackLongMulLocationsSafe, wordStackLongMulLocationSafe,
        wordSpecialArithLocationsSafe, wordStackLongMulMoveToPhysical,
        wordStackLongMulMoveFromPhysical, wordStackJoin, wordStackLocation,
        wordStackOffset, lookupNatInfo, evalWordStackMachine,
        wordStackMachineWriteRegister, wordStackMachineWriteSlot])

end Flapjack.RiscV
