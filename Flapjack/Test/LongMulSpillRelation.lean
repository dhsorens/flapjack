import Flapjack.RiscV.CorrectnessDirectLongMul

/-! Regression coverage for the fully spilled LongMul lowering. -/

namespace Flapjack.RiscV

def longMulSpillConfig : WordStackConfig :=
  { locations := [(0, .stack 2), (1, .stack 3),
      (2, .stack 4), (3, .stack 5), (4, .register 6)]
    scratch := 31
    stackBase := 10
    addressScratch := 29
    specialScratch := 28 }

def longMulSpillState : WordStackMachineState 8 :=
  { registers := fun register => if register = 6 then BitVec.ofNat 8 23 else 0
    stack := fun offset =>
      if offset = 14 then BitVec.ofNat 8 3
      else if offset = 15 then BitVec.ofNat 8 4 else 0
    stores := fun _ => 0
    memory := fun _ => 0
    sharedMemory := fun _ => 0 }

def longMulSpillValues : Nat → Option (Word 8) := fun name =>
  if name = 4 then some (BitVec.ofNat 8 23) else none

example :
    ∀ name value location, name ≠ 0 → name ≠ 1 →
      longMulSpillValues name = some value →
      wordStackLocation longMulSpillConfig name = some location →
      wordStackMachineValue longMulSpillConfig
        (((wordToStackProg (α := Nat) longMulSpillConfig
          (.inst (.arith (.longMul 0 1 2 3)))).bind
          (evalWordStackMachine longMulSpillState)).getD longMulSpillState)
        name = some value := by
  have hvalue_location : ∀ name value location,
      longMulSpillValues name = some value →
      wordStackLocation longMulSpillConfig name = some location →
      name = 4 ∧ value = BitVec.ofNat 8 23 ∧ location = .register 6 := by
    intro name value location hvalue hlocation
    simp [longMulSpillValues] at hvalue
    by_cases hname : name = 4
    · subst name
      simp at hvalue
      subst value
      have hlocation' : location = .register 6 := by
        simpa [longMulSpillConfig, wordStackLocation, lookupNatInfo] using
          hlocation.symm
      exact ⟨rfl, rfl, hlocation'⟩
    · simp [hname] at hvalue
  refine evalWordStackMachine_direct_longMul_spilled_preserves_unrelated_values
    (config := longMulSpillConfig) (state := longMulSpillState)
    (final := ((wordToStackProg (α := Nat) longMulSpillConfig
      (.inst (.arith (.longMul 0 1 2 3)))).bind
      (evalWordStackMachine longMulSpillState)).getD longMulSpillState)
    (destinationLeft := 0) (destinationRight := 1)
    (sourceLeft := 2) (sourceRight := 3)
    (destinationLeftSlot := 2) (destinationRightSlot := 3)
    (sourceLeftSlot := 4) (sourceRightSlot := 5)
    (values := longMulSpillValues)
    (hdestinationLeft := by simp [longMulSpillConfig, wordStackLocation, lookupNatInfo])
    (hdestinationRight := by simp [longMulSpillConfig, wordStackLocation, lookupNatInfo])
    (hsourceLeft := by simp [longMulSpillConfig, wordStackLocation, lookupNatInfo])
    (hsourceRight := by simp [longMulSpillConfig, wordStackLocation, lookupNatInfo])
    (hspecial := by simp [longMulSpillConfig, wordSpecialArithLocationsSafe,
      lookupNatInfo])
    (hreserved := by decide)
    (hvalues := by
      intro name value location hvalue hlocation
      obtain ⟨rfl, rfl, rfl⟩ := hvalue_location name value location hvalue hlocation
      simp [longMulSpillConfig, longMulSpillState, wordStackMachineValue,
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
      simp [longMulSpillConfig, longMulSpillState, wordToStackProg,
        wordToStackInst, wordStackArithInst, wordStackLongMulInst,
        wordStackLongMulLocationsSafe, wordStackLongMulLocationSafe,
        wordSpecialArithLocationsSafe,
        wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
        wordStackJoin, wordStackLocation, wordStackOffset,
        evalWordStackMachine, wordStackMachineWriteRegister,
        wordStackMachineWriteSlot, lookupNatInfo])

example :
    wordStackMachineValue longMulSpillConfig
      (((wordStackLongMulInst longMulSpillConfig
        (.longMul 0 1 2 3)).bind
        (evalWordStackMachine longMulSpillState)).getD longMulSpillState) 4 =
      wordStackMachineValue longMulSpillConfig longMulSpillState 4 := by
  apply evalWordStackMachine_longMul_spilled_preserves_other_value
    (config := longMulSpillConfig) (state := longMulSpillState)
    (final := ((wordStackLongMulInst longMulSpillConfig
      (.longMul 0 1 2 3)).bind
      (evalWordStackMachine longMulSpillState)).getD longMulSpillState)
    (destinationLeft := 0) (destinationRight := 1)
    (sourceLeft := 2) (sourceRight := 3) (other := 4)
    (destinationLeftSlot := 2) (destinationRightSlot := 3)
    (sourceLeftSlot := 4) (sourceRightSlot := 5)
    (otherLocation := .register 6)
  · simp [longMulSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulSpillConfig, wordStackLocation, lookupNatInfo]
  · simp [longMulSpillConfig, wordStackLocation, lookupNatInfo]
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [longMulSpillConfig, longMulSpillState, wordStackLongMulInst,
      wordStackLongMulLocationsSafe, wordStackLongMulLocationSafe,
      wordStackLongMulMoveToPhysical, wordStackLongMulMoveFromPhysical,
      wordStackJoin, wordStackLocation, wordStackOffset, evalWordStackMachine,
      wordStackMachineWriteRegister, wordStackMachineWriteSlot, lookupNatInfo]

end Flapjack.RiscV
